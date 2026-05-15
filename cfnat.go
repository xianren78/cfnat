package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"net/netip"
	"net/url"
	"os"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

const (
	timeout     = 1 * time.Second // 超时时间
	maxDuration = 2 * time.Second // 最大持续时间
)

var (
	activeConnections  int32 // 用于跟踪活跃连接的数量
	validIPClientCache sync.Map
	randomMu           sync.Mutex
	randomGenerator    = rand.New(rand.NewSource(time.Now().UnixNano()))
	runtimeLogger      *RuntimeLogger
)

// IPManager 用于安全管理 IP 地址状态
type IPManager struct {
	mu            sync.RWMutex
	currentIP     string
	ipAddresses   []string
	currentIndex  int
	allIPsChecked bool
}

// RuntimeLogger 控制重要日志与 debug 日志写入文件。
// 非 debug 模式：只有 auditLogf/auditLogln 记录的重要运行日志会写入文件。
// debug 模式：所有 log.Printf/log.Println/log.Fatalf 输出都会同时写入文件。
type RuntimeLogger struct {
	mu     sync.Mutex
	debug  bool
	logger *log.Logger
}

func initRuntimeLogger(logFilePath string, debug bool) (*os.File, error) {
	logFilePath = strings.TrimSpace(logFilePath)
	if logFilePath == "" {
		return nil, nil
	}

	file, err := os.OpenFile(logFilePath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, err
	}

	runtimeLogger = &RuntimeLogger{
		debug:  debug,
		logger: log.New(file, "", log.LstdFlags),
	}

	if debug {
		// 后台运行时，stderr 已经重定向到日志文件；这里直接写 file，避免重复写入。
		if os.Getenv("CFNAT_DAEMONIZED") == "1" {
			log.SetOutput(file)
		} else {
			log.SetOutput(io.MultiWriter(os.Stderr, file))
		}
	}

	return file, nil
}

func auditLogf(format string, args ...interface{}) {
	if runtimeLogger == nil {
		log.Printf(format, args...)
		return
	}
	runtimeLogger.Printf(format, args...)
}

func auditLogln(args ...interface{}) {
	if runtimeLogger == nil {
		log.Println(args...)
		return
	}
	runtimeLogger.Println(args...)
}

func (l *RuntimeLogger) Printf(format string, args ...interface{}) {
	if l == nil {
		log.Printf(format, args...)
		return
	}

	log.Printf(format, args...)
	if l.debug {
		return
	}

	l.mu.Lock()
	defer l.mu.Unlock()
	l.logger.Printf(format, args...)
}

func (l *RuntimeLogger) Println(args ...interface{}) {
	if l == nil {
		log.Println(args...)
		return
	}

	log.Println(args...)
	if l.debug {
		return
	}

	l.mu.Lock()
	defer l.mu.Unlock()
	l.logger.Println(args...)
}

func logSelectedIPList(results []result, currentIP string, currentIndex int) {
	auditLogf("启动选定 IP 列表：共 %d 个候选 IP，currentIP=%s，索引=%d", len(results), currentIP, currentIndex)
	for i, r := range results {
		mark := ""
		if r.ip == currentIP {
			mark = " <- currentIP"
		}
		auditLogf("候选IP[%d]%s IP=%s 数据中心=%s 地区=%s 城市=%s 延迟=%s", i, mark, r.ip, r.dataCenter, r.region, r.city, r.latency)
	}
}

func NewIPManager() *IPManager {
	return &IPManager{}
}

func (m *IPManager) SetIPAddresses(ips []string) {
	m.mu.Lock()
	defer m.mu.Unlock()

	m.ipAddresses = append([]string(nil), ips...)
	m.currentIP = ""
	m.currentIndex = 0
	m.allIPsChecked = false
}

func (m *IPManager) GetCurrentIP() string {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.currentIP
}

func (m *IPManager) SetCurrentIP(ip string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.currentIP = ip
}

func (m *IPManager) SetCurrentIPWithIndex(ip string, index int) {
	m.mu.Lock()
	defer m.mu.Unlock()

	m.currentIP = ip
	m.currentIndex = index
	m.allIPsChecked = false
}

func (m *IPManager) GetIPAddresses() []string {
	m.mu.RLock()
	defer m.mu.RUnlock()

	ips := make([]string, len(m.ipAddresses))
	copy(ips, m.ipAddresses)
	return ips
}

// GetTargetIPs 返回用于当前连接尝试的候选 IP。
// 第一个永远是 currentIP，后面按扫描结果顺序补足，避免重复连接同一个 IP。
func (m *IPManager) GetTargetIPs(num int) []string {
	m.mu.RLock()
	defer m.mu.RUnlock()

	if num <= 0 {
		num = 1
	}

	targets := make([]string, 0, num)
	seen := make(map[string]struct{}, num)

	if m.currentIP != "" {
		targets = append(targets, m.currentIP)
		seen[m.currentIP] = struct{}{}
	}

	for i := m.currentIndex + 1; i < len(m.ipAddresses) && len(targets) < num; i++ {
		ip := m.ipAddresses[i]
		if _, ok := seen[ip]; ok {
			continue
		}
		targets = append(targets, ip)
		seen[ip] = struct{}{}
	}

	// 如果 currentIndex 后面的 IP 不够，则从前面补齐，仍然避免重复。
	for i := 0; i <= m.currentIndex && i < len(m.ipAddresses) && len(targets) < num; i++ {
		ip := m.ipAddresses[i]
		if _, ok := seen[ip]; ok {
			continue
		}
		targets = append(targets, ip)
		seen[ip] = struct{}{}
	}

	return targets
}

// GetCandidateIPs 返回定时选路使用的候选 IP。
// 这里直接取扫描排序后的前 num 个 IP，避免每个客户端连接再做多 IP 竞争。
func (m *IPManager) GetCandidateIPs(num int) []string {
	m.mu.RLock()
	defer m.mu.RUnlock()

	if num <= 0 {
		num = 1
	}
	if num > len(m.ipAddresses) {
		num = len(m.ipAddresses)
	}

	ips := make([]string, num)
	copy(ips, m.ipAddresses[:num])
	return ips
}

// SetCurrentIPByValue 根据 IP 值更新 currentIP，同时修正 currentIndex。
// 返回值：是否发生变化、索引、是否找到该 IP。
func (m *IPManager) SetCurrentIPByValue(ip string) (bool, int, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()

	for i, item := range m.ipAddresses {
		if item == ip {
			changed := m.currentIP != ip
			m.currentIP = ip
			m.currentIndex = i
			m.allIPsChecked = false
			return changed, i, true
		}
	}

	return false, -1, false
}

func (m *IPManager) IsAllIPsChecked() bool {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.allIPsChecked
}

func (m *IPManager) Clear() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ipAddresses = []string{}
	m.currentIP = ""
	m.currentIndex = 0
	m.allIPsChecked = false
}

func (m *IPManager) switchToNextValidIP(useTLS bool, port int, domain string, code int) bool {
	// 不要持有写锁进行网络请求，否则会阻塞 GetCurrentIP / GetTargetIPs。
	m.mu.RLock()
	ips := append([]string(nil), m.ipAddresses...)
	startIndex := m.currentIndex + 1
	currentIP := m.currentIP
	m.mu.RUnlock()

	for i := startIndex; i < len(ips); i++ {
		ip := ips[i]
		if ip == currentIP {
			continue
		}

		if checkValidIP(ip, port, useTLS, domain, code) {
			m.mu.Lock()
			m.currentIP = ip
			m.currentIndex = i
			m.allIPsChecked = false
			m.mu.Unlock()

			auditLogf("切换到新的有效 IP: %s 更新 IP 索引: %d", ip, i)
			return true
		}
	}

	m.mu.Lock()
	m.allIPsChecked = true
	m.mu.Unlock()

	auditLogln("所有 IP 都已检查过，程序将退出")
	return false
}

type result struct {
	ip          string        // IP地址
	dataCenter  string        // 数据中心
	region      string        // 地区
	city        string        // 城市
	latency     string        // 延迟
	tcpDuration time.Duration // TCP请求延迟
}

type location struct {
	Iata   string  `json:"iata"`
	Lat    float64 `json:"lat"`
	Lon    float64 `json:"lon"`
	Cca2   string  `json:"cca2"`
	Region string  `json:"region"`
	City   string  `json:"city"`
}

type CloudflareDNSUpdater struct {
	enabled    bool
	token      string
	zoneID     string
	recordID   string
	recordName string
	proxied    bool
	ttl        int
	client     *http.Client
	mu         sync.Mutex
	lastIP     string
}

type cloudflareDNSRecord struct {
	ID      string `json:"id"`
	Type    string `json:"type"`
	Name    string `json:"name"`
	Content string `json:"content"`
}

type cloudflareDNSRecordResponse struct {
	Success bool                 `json:"success"`
	Errors  []cloudflareAPIError `json:"errors"`
	Result  cloudflareDNSRecord  `json:"result"`
}

type cloudflareDNSRecordListResponse struct {
	Success bool                  `json:"success"`
	Errors  []cloudflareAPIError  `json:"errors"`
	Result  []cloudflareDNSRecord `json:"result"`
}

type cloudflareAPIError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

func NewCloudflareDNSUpdater(enabled bool, token, zoneID, recordID, recordName string, proxied bool, ttl int) *CloudflareDNSUpdater {
	return &CloudflareDNSUpdater{
		enabled:    enabled,
		token:      strings.TrimSpace(token),
		zoneID:     strings.TrimSpace(zoneID),
		recordID:   strings.TrimSpace(recordID),
		recordName: strings.TrimSpace(recordName),
		proxied:    proxied,
		ttl:        ttl,
		client: &http.Client{
			Timeout: 10 * time.Second,
		},
	}
}

func (u *CloudflareDNSUpdater) Enabled() bool {
	return u != nil && u.enabled && u.token != "" && u.zoneID != "" && u.recordName != ""
}

func (u *CloudflareDNSUpdater) UpdateIfChanged(ip string) error {
	if !u.Enabled() {
		return nil
	}

	addr, err := netip.ParseAddr(strings.TrimSpace(ip))
	if err != nil {
		return fmt.Errorf("Cloudflare AAAA 更新失败：无效 IP %q: %w", ip, err)
	}
	if !addr.Is6() {
		return fmt.Errorf("Cloudflare AAAA 更新需要 IPv6，但当前 IP 是 %s", ip)
	}

	ip = addr.String()

	u.mu.Lock()
	defer u.mu.Unlock()

	if u.lastIP == ip {
		auditLogf("Cloudflare AAAA 记录未更新: %s 仍为 %s", u.recordName, ip)
		return nil
	}

	if u.recordID == "" {
		if err := u.findRecordIDLocked(); err != nil {
			return err
		}
	}

	payload := map[string]any{
		"type":    "AAAA",
		"name":    u.recordName,
		"content": ip,
		"proxied": u.proxied,
	}
	if u.ttl > 0 {
		payload["ttl"] = u.ttl
	}

	body, err := json.Marshal(payload)
	if err != nil {
		return err
	}

	apiURL := fmt.Sprintf("https://api.cloudflare.com/client/v4/zones/%s/dns_records/%s", u.zoneID, u.recordID)
	req, err := http.NewRequest(http.MethodPatch, apiURL, bytes.NewReader(body))
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", "Bearer "+u.token)
	req.Header.Set("Content-Type", "application/json")

	resp, err := u.client.Do(req)
	if err != nil {
		return fmt.Errorf("请求 Cloudflare API 失败: %w", err)
	}
	defer resp.Body.Close()

	respBody, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("读取 Cloudflare API 响应失败: %w", err)
	}

	var cfResp cloudflareDNSRecordResponse
	if err := json.Unmarshal(respBody, &cfResp); err != nil {
		return fmt.Errorf("解析 Cloudflare API 响应失败，HTTP %d，响应: %s", resp.StatusCode, string(respBody))
	}

	if resp.StatusCode < 200 || resp.StatusCode >= 300 || !cfResp.Success {
		return fmt.Errorf("Cloudflare AAAA 更新失败，HTTP %d，错误: %s，响应: %s", resp.StatusCode, formatCloudflareErrors(cfResp.Errors), string(respBody))
	}

	u.lastIP = ip
	auditLogf("Cloudflare AAAA 记录已更新: %s -> %s", u.recordName, ip)
	return nil
}

func (u *CloudflareDNSUpdater) findRecordIDLocked() error {
	query := url.Values{}
	query.Set("type", "AAAA")
	query.Set("name", u.recordName)

	apiURL := fmt.Sprintf("https://api.cloudflare.com/client/v4/zones/%s/dns_records?%s", u.zoneID, query.Encode())
	req, err := http.NewRequest(http.MethodGet, apiURL, nil)
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", "Bearer "+u.token)
	resp, err := u.client.Do(req)
	if err != nil {
		return fmt.Errorf("查询 Cloudflare DNS 记录失败: %w", err)
	}
	defer resp.Body.Close()

	respBody, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("读取 Cloudflare DNS 记录查询响应失败: %w", err)
	}

	var cfResp cloudflareDNSRecordListResponse
	if err := json.Unmarshal(respBody, &cfResp); err != nil {
		return fmt.Errorf("解析 Cloudflare DNS 记录查询响应失败，HTTP %d，响应: %s", resp.StatusCode, string(respBody))
	}

	if resp.StatusCode < 200 || resp.StatusCode >= 300 || !cfResp.Success {
		return fmt.Errorf("查询 Cloudflare DNS 记录失败，HTTP %d，错误: %s，响应: %s", resp.StatusCode, formatCloudflareErrors(cfResp.Errors), string(respBody))
	}

	if len(cfResp.Result) == 0 {
		return fmt.Errorf("没有找到 Cloudflare AAAA 记录 %s，请先创建该记录，或使用 -cf-record-id 指定记录 ID", u.recordName)
	}

	u.recordID = cfResp.Result[0].ID
	auditLogf("已找到 Cloudflare AAAA 记录 ID: %s (%s -> %s)", u.recordID, cfResp.Result[0].Name, cfResp.Result[0].Content)
	return nil
}

func formatCloudflareErrors(errors []cloudflareAPIError) string {
	if len(errors) == 0 {
		return "无详细错误"
	}

	parts := make([]string, 0, len(errors))
	for _, err := range errors {
		parts = append(parts, fmt.Sprintf("%d: %s", err.Code, err.Message))
	}
	return strings.Join(parts, "; ")
}

func daemonize(logFilePath string, debug bool) (int, error) {
	exePath, err := os.Executable()
	if err != nil {
		return 0, fmt.Errorf("获取当前可执行文件路径失败: %w", err)
	}

	workDir, err := os.Getwd()
	if err != nil {
		return 0, fmt.Errorf("获取当前工作目录失败: %w", err)
	}

	stdinFile, err := os.OpenFile(os.DevNull, os.O_RDONLY, 0)
	if err != nil {
		return 0, fmt.Errorf("打开 %s 失败: %w", os.DevNull, err)
	}
	defer stdinFile.Close()

	openNullWriter := func() (*os.File, error) {
		return os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	}

	openLogWriter := func() (*os.File, error) {
		if strings.TrimSpace(logFilePath) == "" {
			return openNullWriter()
		}
		return os.OpenFile(logFilePath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	}

	var stdoutFile *os.File
	var stderrFile *os.File

	if debug {
		stdoutFile, err = openLogWriter()
		if err != nil {
			return 0, fmt.Errorf("打开 stdout 日志文件失败: %w", err)
		}
		defer stdoutFile.Close()

		stderrFile, err = openLogWriter()
		if err != nil {
			return 0, fmt.Errorf("打开 stderr 日志文件失败: %w", err)
		}
		defer stderrFile.Close()
	} else {
		// 非 debug 后台模式只通过 auditLog 写关键日志到 log-file，普通 stdout/stderr 丢弃，避免刷日志。
		stdoutFile, err = openNullWriter()
		if err != nil {
			return 0, fmt.Errorf("打开 stdout 重定向失败: %w", err)
		}
		defer stdoutFile.Close()

		stderrFile, err = openNullWriter()
		if err != nil {
			return 0, fmt.Errorf("打开 stderr 重定向失败: %w", err)
		}
		defer stderrFile.Close()
	}

	env := append(os.Environ(), "CFNAT_DAEMONIZED=1")
	attr := &os.ProcAttr{
		Dir:   workDir,
		Env:   env,
		Files: []*os.File{stdinFile, stdoutFile, stderrFile},
		Sys: &syscall.SysProcAttr{
			Setsid: true,
		},
	}

	process, err := os.StartProcess(exePath, os.Args, attr)
	if err != nil {
		return 0, fmt.Errorf("启动后台进程失败: %w", err)
	}

	pid := process.Pid
	if err := process.Release(); err != nil {
		return pid, fmt.Errorf("释放后台进程失败: %w", err)
	}

	return pid, nil
}

func main() {
	localAddr := flag.String("addr", "0.0.0.0:1234", "本地监听的 IP 和端口")
	code := flag.Int("code", 200, "HTTP/HTTPS 响应状态码")
	coloFilter := flag.String("colo", "", "筛选数据中心例如 HKG,SJC,LAX (多个数据中心用逗号隔开,留空则忽略匹配)")
	Delay := flag.Int("delay", 300, "有效延迟（毫秒），超过此延迟将断开连接")
	domain := flag.String("domain", "cloudflaremirrors.com/debian", "响应状态码检查的域名地址")
	ipCount := flag.Int("ipnum", 20, "提取的有效IP数量")
	ipsType := flag.String("ips", "4", "指定生成IPv4还是IPv6地址 (4或6)")
	num := flag.Int("num", 5, "定时选路时并发尝试的候选目标 IP 数量")
	routeInterval := flag.Int("route-interval", 60, "主动筛选最佳 IP 的间隔秒数；小于等于 0 表示关闭定时选路")
	routeThreshold := flag.Int("route-threshold", 50, "定时选路切换阈值毫秒；新 IP 比当前 IP 快超过该值才切换")
	port := flag.Int("port", 443, "转发的目标端口")
	random := flag.Bool("random", true, "是否随机生成IP，如果为false，则从CIDR中拆分出所有IP")
	maxThreads := flag.Int("task", 100, "并发请求最大协程数")
	useTLS := flag.Bool("tls", true, "是否为 TLS 端口")
	cfEnable := flag.Bool("cf-enable", false, "是否启用 Cloudflare AAAA 记录更新")
	cfToken := flag.String("cf-token", os.Getenv("CLOUDFLARE_API_TOKEN"), "Cloudflare API Token，也可用环境变量 CLOUDFLARE_API_TOKEN")
	cfZoneID := flag.String("cf-zone-id", os.Getenv("CLOUDFLARE_ZONE_ID"), "Cloudflare Zone ID，也可用环境变量 CLOUDFLARE_ZONE_ID")
	cfRecordID := flag.String("cf-record-id", os.Getenv("CLOUDFLARE_RECORD_ID"), "Cloudflare DNS Record ID，可选；为空时按记录名自动查询，也可用环境变量 CLOUDFLARE_RECORD_ID")
	cfRecordName := flag.String("cf-record-name", "cf.48521.xyz", "需要更新的 Cloudflare AAAA 记录名")
	cfProxied := flag.Bool("cf-proxied", false, "Cloudflare DNS 记录是否开启代理")
	cfTTL := flag.Int("cf-ttl", 1, "Cloudflare DNS TTL，1 表示自动")
	logFile := flag.String("log-file", "cfnat.log", "日志文件路径；为空表示不写日志文件")
	debugLog := flag.Bool("debug", false, "debug 模式：将全部 log 输出同时写入日志文件")
	daemonMode := flag.Bool("d", false, "后台运行模式；父进程启动后台子进程后退出")

	flag.Parse()

	if *daemonMode && os.Getenv("CFNAT_DAEMONIZED") != "1" {
		pid, err := daemonize(*logFile, *debugLog)
		if err != nil {
			log.Fatalf("后台运行启动失败: %v", err)
		}
		fmt.Printf("已后台运行，PID: %d，日志文件: %s\n", pid, *logFile)
		return
	}

	logHandle, err := initRuntimeLogger(*logFile, *debugLog)
	if err != nil {
		log.Fatalf("无法打开日志文件 %s: %v", *logFile, err)
	}
	if logHandle != nil {
		defer logHandle.Close()
		auditLogf("日志文件已启用: %s，debug=%v，daemon=%v", *logFile, *debugLog, os.Getenv("CFNAT_DAEMONIZED") == "1")
	}

	cfUpdater := NewCloudflareDNSUpdater(*cfEnable, *cfToken, *cfZoneID, *cfRecordID, *cfRecordName, *cfProxied, *cfTTL)
	if cfUpdater.Enabled() {
		auditLogf("Cloudflare AAAA 自动更新已启用，记录名: %s", *cfRecordName)
	} else if *cfEnable {
		auditLogln("Cloudflare AAAA 自动更新未启用：请提供 -cf-token、-cf-zone-id，并确认 -cf-record-name 不为空")
	}

	ipManager := NewIPManager()

	listener, err := net.Listen("tcp", *localAddr)
	if err != nil {
		log.Fatalf("无法监听 %s: %v", *localAddr, err)
	}
	defer listener.Close()

	auditLogf("正在监听 %s，定时选路候选数：%d，选路间隔：%d 秒，切换阈值：%d ms，有效延迟：%d ms", *localAddr, *num, *routeInterval, *routeThreshold, *Delay)

	for {
		startTime := time.Now()

		locations, err := loadLocations()
		if err != nil {
			log.Printf("加载位置信息失败: %v", err)
			time.Sleep(3 * time.Second)
			continue
		}

		locationMap := make(map[string]location)
		for _, loc := range locations {
			locationMap[loc.Iata] = loc
		}

		var url string
		var filename string

		switch *ipsType {
		case "6":
			filename = "ips-v6.txt"
			url = "https://www.baipiao.eu.org/cloudflare/ips-v6"
		case "4":
			filename = "ips-v4.txt"
			url = "https://www.baipiao.eu.org/cloudflare/ips-v4"
		default:
			fmt.Println("无效的IP类型。请使用 '4' 或 '6'")
			return
		}

		var content string

		if _, err = os.Stat(filename); os.IsNotExist(err) {
			fmt.Printf("文件 %s 不存在，正在从 URL %s 下载数据\n", filename, url)
			content, err = getURLContent(url)
			if err != nil {
				fmt.Println("获取URL内容出错:", err)
				return
			}
			err = saveToFile(filename, content)
			if err != nil {
				fmt.Println("保存文件出错:", err)
				return
			}
		} else {
			content, err = getFileContent(filename)
			if err != nil {
				fmt.Println("读取本地文件出错:", err)
				return
			}
		}

		var ipList []string
		if *random {
			ipList = parseIPList(content)
			switch *ipsType {
			case "6":
				ipList = getRandomIPv6s(ipList)
			case "4":
				ipList = getRandomIPv4s(ipList)
			}
		} else {
			ipList, err = readIPs(filename)
			if err != nil {
				fmt.Println("读取IP出错:", err)
				return
			}
		}

		results := scanIPs(ipList, locationMap, *maxThreads)

		if len(results) == 0 {
			fmt.Println("未发现有效IP")
			time.Sleep(3 * time.Second)
			continue
		}

		if *coloFilter != "" {
			filters := strings.Split(*coloFilter, ",")
			var filteredResults []result
			for _, r := range results {
				for _, filter := range filters {
					if strings.EqualFold(r.dataCenter, strings.TrimSpace(filter)) {
						filteredResults = append(filteredResults, r)
						break
					}
				}
			}
			results = filteredResults
		}

		sort.Slice(results, func(i, j int) bool {
			return results[i].tcpDuration < results[j].tcpDuration
		})

		if len(results) > *ipCount {
			results = results[:*ipCount]
		}

		fmt.Println("IP 地址 | 数据中心 | 地区 | 城市 | 延迟")
		for _, r := range results {
			fmt.Printf("%s | %s | %s | %s | %s\n", r.ip, r.dataCenter, r.region, r.city, r.latency)
		}

		fmt.Printf("成功提取 %d 个有效IP，耗时 %d秒\n", len(results), time.Since(startTime)/time.Second)

		var ips []string
		for _, r := range results {
			ips = append(ips, r.ip)
		}
		ipManager.SetIPAddresses(ips)

		currentIP, currentIndex := selectValidIP(ipManager, *useTLS, *port, *domain, *code)
		if currentIP == "" {
			log.Printf("没有有效的 IP 可用")
			continue
		}
		ipManager.SetCurrentIPWithIndex(currentIP, currentIndex)
		logSelectedIPList(results, currentIP, currentIndex)
		if err := cfUpdater.UpdateIfChanged(currentIP); err != nil {
			auditLogf("更新 Cloudflare AAAA 记录失败: %v", err)
		}

		ctx, cancel := context.WithCancel(context.Background())
		done := make(chan bool)

		var loopWG sync.WaitGroup
		loopWG.Add(3)

		go func() {
			defer loopWG.Done()
			statusCheck(ctx, *useTLS, *port, done, *domain, *code, time.Duration(*Delay)*time.Millisecond, ipManager, cfUpdater)
		}()

		go func() {
			defer loopWG.Done()
			periodicRouteSelector(ctx, time.Duration(*routeInterval)*time.Second, *num, *port, time.Duration(*Delay)*time.Millisecond, time.Duration(*routeThreshold)*time.Millisecond, ipManager, cfUpdater)
		}()

		go func() {
			defer loopWG.Done()
			for {
				select {
				case <-ctx.Done():
					log.Println("连接接受 goroutine 收到退出信号")
					return
				default:
					if tcpListener, ok := listener.(*net.TCPListener); ok {
						tcpListener.SetDeadline(time.Now().Add(1 * time.Second))
					}
					conn, err := listener.Accept()
					if err != nil {
						if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
							continue
						}
						if opErr, ok := err.(*net.OpError); ok && opErr.Err.Error() == "use of closed network connection" {
							return
						}
						log.Printf("接受连接时发生错误: %v", err)
						continue
					}

					clientAddr := conn.RemoteAddr().String()
					atomic.AddInt32(&activeConnections, 1)
					log.Printf("客户端来源: %s 连接建立，当前活跃连接数: %d", clientAddr, atomic.LoadInt32(&activeConnections))

					currentIP := ipManager.GetCurrentIP()
					if currentIP == "" {
						log.Println("当前没有可用目标 IP，关闭客户端连接")
						conn.Close()
						atomic.AddInt32(&activeConnections, -1)
						continue
					}

					go handleConnection(conn, []string{makeTargetAddr(currentIP, *port)}, time.Duration(*Delay)*time.Millisecond)
				}
			}
		}()

		<-done
		cancel()
		loopWG.Wait()

		ipManager.Clear()
		validIPClientCache = sync.Map{}
		log.Println("主函数将退出当前循环，因为所有 IP 都已用尽")
	}
}

// loadLocations 加载位置信息，使用函数封装确保 defer 正确执行
func loadLocations() ([]location, error) {
	var locations []location

	if _, err := os.Stat("locations.json"); os.IsNotExist(err) {
		fmt.Println("本地 locations.json 不存在\n正在从 https://www.baipiao.eu.org/cloudflare/locations 下载 locations.json")
		resp, err := http.Get("https://www.baipiao.eu.org/cloudflare/locations")
		if err != nil {
			return nil, fmt.Errorf("无法从URL中获取JSON: %v", err)
		}
		defer resp.Body.Close()

		body, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, fmt.Errorf("无法读取响应体: %v", err)
		}

		err = json.Unmarshal(body, &locations)
		if err != nil {
			return nil, fmt.Errorf("无法解析JSON: %v", err)
		}

		file, err := os.Create("locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法创建文件: %v", err)
		}
		defer file.Close()

		_, err = file.Write(body)
		if err != nil {
			return nil, fmt.Errorf("无法写入文件: %v", err)
		}
	} else {
		file, err := os.Open("locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法打开文件: %v", err)
		}
		defer file.Close()

		body, err := io.ReadAll(file)
		if err != nil {
			return nil, fmt.Errorf("无法读取文件: %v", err)
		}

		err = json.Unmarshal(body, &locations)
		if err != nil {
			return nil, fmt.Errorf("无法解析JSON: %v", err)
		}
	}

	return locations, nil
}

// scanIPs 扫描 IP 列表并返回结果
func scanIPs(ipList []string, locationMap map[string]location, maxThreads int) []result {
	var wg sync.WaitGroup
	var mu sync.Mutex
	var results []result

	thread := make(chan struct{}, maxThreads)

	var count int32
	total := len(ipList)

	for _, ip := range ipList {
		wg.Add(1)
		thread <- struct{}{}
		go func(ipAddr string) {
			defer func() {
				<-thread
				wg.Done()
				current := atomic.AddInt32(&count, 1)
				percentage := float64(current) / float64(total) * 100
				fmt.Printf("已完成: %d 总数: %d 已完成: %.2f%%\r", current, total, percentage)
				if int(current) == total {
					fmt.Printf("已完成: %d 总数: %d 已完成: %.2f%%\n", current, total, percentage)
				}
			}()

			dialer := &net.Dialer{
				Timeout:   timeout,
				KeepAlive: 0,
			}
			start := time.Now()
			conn, err := dialer.Dial("tcp", net.JoinHostPort(ipAddr, "80"))
			if err != nil {
				return
			}
			defer conn.Close()

			tcpDuration := time.Since(start)

			requestURL := "http://" + net.JoinHostPort(ipAddr, "80")
			req, err := http.NewRequest("GET", requestURL, nil)
			if err != nil {
				return
			}
			req.Header.Set("User-Agent", "Mozilla/5.0")
			req.Close = true

			conn.SetDeadline(time.Now().Add(maxDuration))
			err = req.Write(conn)
			if err != nil {
				return
			}

			reader := bufio.NewReader(conn)
			resp, err := http.ReadResponse(reader, req)
			if err != nil {
				return
			}
			defer resp.Body.Close()

			cfRay := strings.TrimSpace(resp.Header.Get("CF-RAY"))
			if cfRay == "" {
				return
			}

			parts := strings.Split(cfRay, "-")
			if len(parts) < 2 {
				return
			}

			dataCenter := strings.TrimSpace(parts[len(parts)-1])
			if dataCenter == "" {
				return
			}

			loc, ok := locationMap[dataCenter]
			mu.Lock()
			if ok {
				fmt.Printf("发现有效IP %s 位置信息 %s 延迟 %d 毫秒\n", ipAddr, loc.City, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, loc.Region, loc.City, fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			} else {
				fmt.Printf("发现有效IP %s 位置信息未知 延迟 %d 毫秒\n", ipAddr, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, "", "", fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			}
			mu.Unlock()
		}(ip)
	}

	wg.Wait()
	return results
}

// 获取URL内容
func getURLContent(url string) (string, error) {
	resp, err := http.Get(url)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("HTTP请求失败，状态码: %d", resp.StatusCode)
	}

	var content strings.Builder
	scanner := bufio.NewScanner(resp.Body)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			content.WriteString(line + "\n")
		}
	}
	if err := scanner.Err(); err != nil {
		return "", err
	}

	return content.String(), nil
}

// 从本地文件读取内容
func getFileContent(filename string) (string, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return "", err
	}
	return string(data), nil
}

// 将内容保存到本地文件
func saveToFile(filename, content string) error {
	return os.WriteFile(filename, []byte(content), 0644)
}

// 解析IP列表，跳过空行
func parseIPList(content string) []string {
	scanner := bufio.NewScanner(strings.NewReader(content))
	var ipList []string
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			ipList = append(ipList, line)
		}
	}
	return ipList
}

func nextRandomIntn(n int) int {
	randomMu.Lock()
	defer randomMu.Unlock()
	return randomGenerator.Intn(n)
}

// 从每个/24子网随机提取一个IPv4
func getRandomIPv4s(ipList []string) []string {
	var randomIPs []string
	for _, subnet := range ipList {
		subnet = strings.TrimSpace(subnet)
		if subnet == "" {
			continue
		}
		baseIP := strings.TrimSuffix(subnet, "/24")
		octets := strings.Split(baseIP, ".")
		if len(octets) >= 4 {
			octets[3] = fmt.Sprintf("%d", nextRandomIntn(256))
			randomIP := strings.Join(octets, ".")
			randomIPs = append(randomIPs, randomIP)
		}
	}
	return randomIPs
}

// 根据父 CIDR 生成其中第 index 个 targetBits 子网
func makeSubPrefix(parent netip.Prefix, targetBits int, index uint64) netip.Prefix {
	parent = parent.Masked()

	ipBytes := parent.Addr().As16()
	parentBits := parent.Bits()
	diff := targetBits - parentBits

	for i := 0; i < diff; i++ {
		bitValue := (index >> uint(diff-1-i)) & 1

		bitPos := parentBits + i
		byteIndex := bitPos / 8
		bitIndex := 7 - (bitPos % 8)

		if bitValue == 1 {
			ipBytes[byteIndex] |= byte(1 << bitIndex)
		} else {
			ipBytes[byteIndex] &^= byte(1 << bitIndex)
		}
	}

	return netip.PrefixFrom(netip.AddrFrom16(ipBytes), targetBits).Masked()
}

// 在指定 IPv6 CIDR 内随机生成一个 IPv6
func randomIPv6InPrefix(prefix netip.Prefix) string {
	prefix = prefix.Masked()

	ipBytes := prefix.Addr().As16()
	bits := prefix.Bits()

	fullBytes := bits / 8
	remainBits := bits % 8

	if fullBytes >= 16 {
		return prefix.Addr().String()
	}

	start := fullBytes

	if remainBits != 0 {
		keepMask := byte(0xff << uint(8-remainBits))
		randomMask := ^keepMask

		randomPart := byte(nextRandomIntn(1 << uint(8-remainBits)))

		ipBytes[fullBytes] = (ipBytes[fullBytes] & keepMask) | (randomPart & randomMask)

		start = fullBytes + 1
	}

	for i := start; i < 16; i++ {
		ipBytes[i] = byte(nextRandomIntn(256))
	}

	return netip.AddrFrom16(ipBytes).String()
}

// 如果掩码 < 52，则从每个 /52 中随机提取一个 IPv6
// 如果掩码 >= 52，则从当前 CIDR 中随机提取一个 IPv6
func getRandomIPv6s(ipList []string) []string {
	var randomIPs []string

	for _, subnet := range ipList {
		subnet = strings.TrimSpace(subnet)
		if subnet == "" {
			continue
		}

		prefix, err := netip.ParsePrefix(subnet)
		if err != nil {
			continue
		}

		if !prefix.Addr().Is6() {
			continue
		}

		prefix = prefix.Masked()
		bits := prefix.Bits()

		if bits < 52 {
			count := uint64(1) << uint(52-bits)

			for i := uint64(0); i < count; i++ {
				p52 := makeSubPrefix(prefix, 52, i)
				randomIPs = append(randomIPs, randomIPv6InPrefix(p52))
			}
		} else {
			randomIPs = append(randomIPs, randomIPv6InPrefix(prefix))
		}
	}

	return randomIPs
}

// 从CIDR中拆分出所有IP
func readIPs(filename string) ([]string, error) {
	file, err := os.Open(filename)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var ips []string
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		if strings.Contains(line, "/") {
			ipAddr, ipNet, err := net.ParseCIDR(line)
			if err != nil {
				return nil, err
			}
			for currentIP := ipAddr.Mask(ipNet.Mask); ipNet.Contains(currentIP); incrementIP(currentIP) {
				ips = append(ips, currentIP.String())
			}
		} else {
			ips = append(ips, line)
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, err
	}

	return ips, nil
}

// 增加IP
func incrementIP(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 {
			break
		}
	}
}

func makeTargetAddr(ip string, port int) string {
	return net.JoinHostPort(ip, fmt.Sprintf("%d", port))
}

func generateTargets(ips []string, port int) []string {
	targets := make([]string, 0, len(ips))
	seen := make(map[string]struct{}, len(ips))

	for _, ip := range ips {
		ip = strings.TrimSpace(ip)
		if ip == "" {
			continue
		}
		if _, ok := seen[ip]; ok {
			continue
		}
		seen[ip] = struct{}{}
		targets = append(targets, makeTargetAddr(ip, port))
	}

	return targets
}

func checkValidIP(ip string, port int, useTLS bool, domain string, code int) bool {
	address := ip
	if strings.Contains(ip, ":") {
		address = fmt.Sprintf("[%s]", ip)
	}
	targetURL := fmt.Sprintf("http://%s", domain)
	if useTLS {
		targetURL = fmt.Sprintf("https://%s", domain)
	}

	cacheKey := fmt.Sprintf("%s:%d", address, port)
	clientAny, loaded := validIPClientCache.Load(cacheKey)
	var client *http.Client
	if loaded {
		client = clientAny.(*http.Client)
	} else {
		transport := &http.Transport{
			TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				dialer := &net.Dialer{Timeout: 2 * time.Second}
				return dialer.DialContext(ctx, network, fmt.Sprintf("%s:%d", address, port))
			},
		}
		newClient := &http.Client{
			Timeout:   2 * time.Second,
			Transport: transport,
		}
		actual, _ := validIPClientCache.LoadOrStore(cacheKey, newClient)
		client = actual.(*http.Client)
	}

	resp, err := client.Get(targetURL)
	if err != nil {
		log.Printf("检查 IP 失败: %s -> %s，错误: %v", ip, targetURL, err)
		return false
	}
	defer resp.Body.Close()

	if resp.StatusCode != code {
		log.Printf("检查 IP 失败: %s -> %s，状态码: %d，期望: %d", ip, targetURL, resp.StatusCode, code)
		return false
	}

	return true
}

func selectValidIP(ipManager *IPManager, useTLS bool, port int, domain string, code int) (string, int) {
	ips := ipManager.GetIPAddresses()
	for i, ip := range ips {
		if checkValidIP(ip, port, useTLS, domain, code) {
			return ip, i
		}
	}
	return "", -1
}

func statusCheck(ctx context.Context, useTLS bool, port int, done chan bool, domain string, code int, delay time.Duration, ipManager *IPManager, cfUpdater *CloudflareDNSUpdater) {
	interval := 2 * time.Second
	if delay > interval {
		interval = delay
	}

	ticker := time.NewTicker(interval)
	defer ticker.Stop()

	failCount := 0
	wasUnhealthy := false
	lastLoggedIP := ""
	auditLogf("状态检查已启动：间隔=%d ms，失败阈值=2 次", interval.Milliseconds())

	for {
		select {
		case <-ctx.Done():
			auditLogln("状态检查收到退出信号")
			return
		case <-ticker.C:
			currentIP := ipManager.GetCurrentIP()
			if currentIP == "" {
				failCount++
				wasUnhealthy = true
				if failCount == 1 {
					auditLogln("状态检查异常: 当前没有可用 IP")
				}
			} else if checkValidIP(currentIP, port, useTLS, domain, code) {
				if wasUnhealthy || failCount > 0 || currentIP != lastLoggedIP {
					auditLogf("状态检查正常: 当前 IP %s", currentIP)
				}
				failCount = 0
				wasUnhealthy = false
				lastLoggedIP = currentIP
			} else {
				failCount++
				wasUnhealthy = true
				auditLogf("状态检查失败 (%d/2)，当前 IP: %s", failCount, currentIP)
			}

			if failCount >= 2 {
				oldIP := currentIP
				auditLogf("连续两次状态检查失败，准备切换 IP，当前 IP: %s", oldIP)

				if !ipManager.switchToNextValidIP(useTLS, port, domain, code) {
					auditLogln("所有 IP 都已检查过，状态检查停止")
					done <- true
					return
				}

				newIP := ipManager.GetCurrentIP()
				auditLogf("状态检查已切换 IP: %s -> %s", oldIP, newIP)

				if err := cfUpdater.UpdateIfChanged(newIP); err != nil {
					auditLogf("更新 Cloudflare AAAA 记录失败: %v", err)
				}

				failCount = 0
				wasUnhealthy = false
				lastLoggedIP = newIP
			}
		}
	}
}

func measureIPDelay(ip string, port int, delay time.Duration) (time.Duration, bool) {
	ip = strings.TrimSpace(ip)
	if ip == "" {
		return 0, false
	}

	start := time.Now()
	conn, err := net.DialTimeout("tcp", makeTargetAddr(ip, port), delay)
	elapsed := time.Since(start)
	if err != nil {
		return elapsed, false
	}
	conn.Close()
	return elapsed, true
}

func selectFastestIPByDial(ips []string, port int, delay time.Duration) (string, time.Duration, bool) {
	if len(ips) == 0 {
		return "", 0, false
	}

	type dialResult struct {
		ip    string
		delay time.Duration
		ok    bool
	}

	results := make(chan dialResult, len(ips))

	for _, ip := range ips {
		ip := strings.TrimSpace(ip)
		if ip == "" {
			results <- dialResult{}
			continue
		}

		go func(candidateIP string) {
			elapsed, ok := measureIPDelay(candidateIP, port, delay)
			results <- dialResult{ip: candidateIP, delay: elapsed, ok: ok}
		}(ip)
	}

	var bestIP string
	var bestDelay time.Duration

	for i := 0; i < len(ips); i++ {
		res := <-results
		if !res.ok {
			continue
		}
		if bestIP == "" || res.delay < bestDelay {
			bestIP = res.ip
			bestDelay = res.delay
		}
	}

	if bestIP == "" {
		return "", 0, false
	}
	return bestIP, bestDelay, true
}

// periodicRouteSelector 每隔固定时间主动从候选 IP 中选出 TCP 建连最快的 IP。
// 只有新 IP 比当前 currentIP 快超过 routeThreshold 时才切换；如果当前 IP 无法连接，则忽略阈值直接切换。
func periodicRouteSelector(ctx context.Context, interval time.Duration, num int, port int, delay time.Duration, routeThreshold time.Duration, ipManager *IPManager, cfUpdater *CloudflareDNSUpdater) {
	if interval <= 0 {
		auditLogln("定时选路已关闭")
		<-ctx.Done()
		return
	}

	if routeThreshold < 0 {
		routeThreshold = 0
	}

	runSelect := func(reason string) {
		candidates := ipManager.GetCandidateIPs(num)
		currentIP := ipManager.GetCurrentIP()

		auditLogf(
			"定时选路开始：原因=%s，候选数=%d，currentIP=%s，连接超时=%d ms，切换阈值=%d ms",
			reason,
			len(candidates),
			currentIP,
			delay.Milliseconds(),
			routeThreshold.Milliseconds(),
		)

		if len(candidates) == 0 {
			auditLogln("定时选路结束：没有候选 IP")
			return
		}

		bestIP, bestDelay, ok := selectFastestIPByDial(candidates, port, delay)
		if !ok {
			auditLogf("定时选路失败：%d 个候选 IP 均无法在 %d ms 内连接", len(candidates), delay.Milliseconds())
			return
		}

		if currentIP == "" {
			changed, index, found := ipManager.SetCurrentIPByValue(bestIP)
			if !found {
				auditLogf("定时选路选出的 IP 不在候选列表中: %s", bestIP)
				return
			}
			if changed {
				auditLogf("定时选路设置当前 IP: %s 延迟 %d ms 索引 %d", bestIP, bestDelay.Milliseconds(), index)
				if err := cfUpdater.UpdateIfChanged(bestIP); err != nil {
					auditLogf("更新 Cloudflare AAAA 记录失败: %v", err)
				}
			} else {
				auditLogf("定时选路结束：currentIP 为空但 SetCurrentIP 未发生变化，bestIP=%s", bestIP)
			}
			return
		}

		currentDelay, currentOK := measureIPDelay(currentIP, port, delay)
		if !currentOK {
			if bestIP == currentIP {
				auditLogf("定时选路结束：当前 IP %s 检测失败，但最快候选仍是当前 IP，保持不变", currentIP)
				return
			}

			changed, index, found := ipManager.SetCurrentIPByValue(bestIP)
			if !found {
				auditLogf("定时选路选出的 IP 不在候选列表中: %s", bestIP)
				return
			}

			if changed {
				auditLogf("定时选路检测到当前 IP 不可用，切换到: %s 延迟 %d ms 索引 %d", bestIP, bestDelay.Milliseconds(), index)
				if err := cfUpdater.UpdateIfChanged(bestIP); err != nil {
					auditLogf("更新 Cloudflare AAAA 记录失败: %v", err)
				}
			} else {
				auditLogf("定时选路结束：当前 IP 不可用，但目标 IP 未变化: %s", bestIP)
			}
			return
		}

		if bestIP == currentIP {
			auditLogf("定时选路完成：保持当前 IP %s，当前延迟 %d ms，最快候选延迟 %d ms", currentIP, currentDelay.Milliseconds(), bestDelay.Milliseconds())
			return
		}

		improvement := currentDelay - bestDelay
		if improvement <= routeThreshold {
			auditLogf(
				"定时选路完成：保持当前 IP %s，新候选 %s，当前延迟 %d ms，新延迟 %d ms，改善 %d ms，未超过阈值 %d ms",
				currentIP,
				bestIP,
				currentDelay.Milliseconds(),
				bestDelay.Milliseconds(),
				improvement.Milliseconds(),
				routeThreshold.Milliseconds(),
			)
			return
		}

		changed, index, found := ipManager.SetCurrentIPByValue(bestIP)
		if !found {
			auditLogf("定时选路选出的 IP 不在候选列表中: %s", bestIP)
			return
		}

		if changed {
			auditLogf("定时选路更新当前 IP: %s -> %s，延迟 %d ms -> %d ms，改善 %d ms，超过阈值 %d ms，索引 %d", currentIP, bestIP, currentDelay.Milliseconds(), bestDelay.Milliseconds(), improvement.Milliseconds(), routeThreshold.Milliseconds(), index)
			if err := cfUpdater.UpdateIfChanged(bestIP); err != nil {
				auditLogf("更新 Cloudflare AAAA 记录失败: %v", err)
			}
		} else {
			auditLogf("定时选路完成：目标 IP 与当前记录一致，保持 %s", bestIP)
		}
	}

	// 启动后立即选一次，后续每 interval 选一次。
	runSelect("startup")

	ticker := time.NewTicker(interval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			auditLogln("定时选路收到退出信号")
			return
		case <-ticker.C:
			runSelect("interval")
		}
	}
}

// 处理客户端连接，尝试连接到指定的转发地址，并选择延迟最低的连接
func handleConnection(conn net.Conn, forwardAddrs []string, delay time.Duration) {
	defer func() {
		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, -1)
		log.Printf("客户端来源: %s 连接关闭，当前活跃连接数: %d", clientAddr, atomic.LoadInt32(&activeConnections))
		conn.Close()
	}()

	if len(forwardAddrs) == 0 {
		log.Println("未提供转发地址，关闭客户端连接")
		return
	}

	if len(forwardAddrs) == 1 {
		forwardConn, err := net.DialTimeout("tcp", forwardAddrs[0], delay)
		if err != nil {
			log.Printf("连接到当前 IP 失败: %s，错误: %v", forwardAddrs[0], err)
			return
		}
		pipeConnections(conn, forwardConn)
		return
	}

	type connResult struct {
		conn   net.Conn
		addr   string
		delay  time.Duration
		errMsg string
	}

	results := make(chan connResult, len(forwardAddrs))

	for _, addr := range forwardAddrs {
		go func(targetAddr string) {
			start := time.Now()
			forwardConn, err := net.DialTimeout("tcp", targetAddr, delay)
			elapsed := time.Since(start)

			if err != nil {
				results <- connResult{nil, targetAddr, elapsed, fmt.Sprintf("连接到 %s 的延迟超过有效值 %d ms", targetAddr, delay.Milliseconds())}
				return
			}

			results <- connResult{forwardConn, targetAddr, elapsed, ""}
		}(addr)
	}

	var validConns []connResult
	var bestConn net.Conn
	var bestDelay time.Duration
	var bestAddr string

	for i := 0; i < len(forwardAddrs); i++ {
		res := <-results
		if res.conn != nil {
			validConns = append(validConns, res)

			if bestConn == nil || res.delay < bestDelay {
				if bestConn != nil {
					bestConn.Close()
				}
				bestConn = res.conn
				bestDelay = res.delay
				bestAddr = res.addr
			} else {
				res.conn.Close()
			}
		} else {
			log.Printf("错误: %s", res.errMsg)
		}
	}

	log.Println("符合要求的连接:")
	for _, vc := range validConns {
		log.Printf("地址: %s 延迟: %d ms", vc.addr, vc.delay.Milliseconds())
	}

	if bestConn != nil {
		log.Printf("选择最佳连接: 地址: %s 延迟: %d ms", bestAddr, bestDelay.Milliseconds())
		pipeConnections(conn, bestConn)
	} else {
		log.Println("未找到符合延迟要求的连接，关闭客户端连接")
	}
}

func pipeConnections(src, dst net.Conn) {
	var wg sync.WaitGroup
	var closeOnce sync.Once
	closeBoth := func() {
		closeOnce.Do(func() {
			src.Close()
			dst.Close()
		})
	}

	wg.Add(2)

	go func() {
		defer wg.Done()
		_, _ = io.Copy(src, dst)
		closeBoth()
	}()

	go func() {
		defer wg.Done()
		_, _ = io.Copy(dst, src)
		closeBoth()
	}()

	wg.Wait()
}
