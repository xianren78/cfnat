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
	"path/filepath"
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
	activeConnections int32 // 用于跟踪活跃连接的数量
	randomMu          sync.Mutex
	randomGenerator   = rand.New(rand.NewSource(time.Now().UnixNano()))
	runtimeLogger     *RuntimeLogger
	error1034Check    *error1034Validator // 启动前设置，运行期间只读
)

type error1034Validator struct {
	url  string
	port string
}

// 请求的 Host 和 TLS SNI 保持为 URL 域名，仅将 TCP 连接定向到待验证的 IP。
func (v *error1034Validator) valid(ip string) bool {
	if v == nil {
		return true
	}
	transport := &http.Transport{
		DisableKeepAlives: true,
		ForceAttemptHTTP2: true,
		Proxy:             nil,
		DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
			return (&net.Dialer{}).DialContext(ctx, "tcp", net.JoinHostPort(ip, v.port))
		},
	}
	defer transport.CloseIdleConnections()
	client := &http.Client{
		Timeout:   5 * time.Second,
		Transport: transport,
		CheckRedirect: func(req *http.Request, via []*http.Request) error {
			return http.ErrUseLastResponse
		},
	}
	resp, err := client.Get(v.url)
	if err != nil {
		auditLogf("1034 验证失败，排除 IP %s: %v", ip, err)
		return false
	}
	defer resp.Body.Close()
	if resp.ProtoMajor != 2 {
		auditLogf("1034 验证未协商到 HTTP/2，排除 IP %s: 协议=%s", ip, resp.Proto)
		return false
	}
	body, err := io.ReadAll(io.LimitReader(resp.Body, 1024*1024))
	if err != nil {
		auditLogf("1034 验证读取失败，排除 IP %s: %v", ip, err)
		return false
	}
	if bytes.Contains(bytes.ToLower(body), []byte("error code: 1034")) {
		auditLogf("IP %s 返回 error code: 1034，排除该 IP", ip)
		return false
	}
	return true
}

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

const logRetention = 24 * time.Hour

// retainedLogWriter 串行处理写入和清理，所有日志入口共用同一文件句柄。
type retainedLogWriter struct {
	mu           sync.Mutex
	file         *os.File
	path         string
	untimedSince time.Time
	stop         chan struct{}
	done         chan struct{}
	closeOnce    sync.Once
	closeErr     error
	closed       bool
}

func newRetainedLogWriter(path string) (*retainedLogWriter, error) {
	file, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, err
	}
	info, err := file.Stat()
	if err != nil {
		file.Close()
		return nil, err
	}
	w := &retainedLogWriter{file: file, path: path, untimedSince: info.ModTime(), stop: make(chan struct{}), done: make(chan struct{})}
	if err := w.prune(time.Now()); err != nil {
		file.Close()
		return nil, err
	}
	go func() {
		defer close(w.done)
		ticker := time.NewTicker(10 * time.Minute)
		defer ticker.Stop()
		for {
			select {
			case <-w.stop:
				return
			case now := <-ticker.C:
				if err := w.prune(now); err != nil {
					auditLogf("清理超过 24 小时的日志失败: %v", err)
				}
			}
		}
	}()
	return w, nil
}

func (w *retainedLogWriter) Write(p []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()
	if w.closed {
		return 0, os.ErrClosed
	}
	return w.file.Write(p)
}

// 根据每条日志的时间戳清理；多行日志的续行沿用上一条记录的时间。
// 新文件写入成功后才替换原文件，清理出错时保留原日志。
func (w *retainedLogWriter) prune(now time.Time) error {
	w.mu.Lock()
	defer w.mu.Unlock()
	if w.closed {
		return os.ErrClosed
	}
	input, err := os.Open(w.path)
	if err != nil {
		return err
	}
	defer input.Close()
	info, err := input.Stat()
	if err != nil {
		return err
	}
	if info.Size() == 0 {
		return nil
	}
	tmp, err := os.CreateTemp(filepath.Dir(w.path), ".cfnat-log-*")
	if err != nil {
		return err
	}
	tmpPath := tmp.Name()
	defer os.Remove(tmpPath)
	defer tmp.Close()
	if err := tmp.Chmod(info.Mode().Perm()); err != nil {
		return err
	}
	reader := bufio.NewReader(input)
	writer := bufio.NewWriter(tmp)
	cutoff := now.Truncate(time.Second).Add(-logRetention)
	keep := !w.untimedSince.Before(cutoff)
	sawTimestamp, changed := false, false
	for {
		line, readErr := reader.ReadString('\n')
		if len(line) > 0 {
			if len(line) >= 19 {
				if stamp, err := time.ParseInLocation("2006/01/02 15:04:05", line[:19], time.Local); err == nil {
					keep = !stamp.Before(cutoff)
					sawTimestamp = true
				}
			}
			if keep {
				if !sawTimestamp {
					// 兼容旧版 debug 中未带时间的输出，只在迁移时使用旧文件修改时间。
					line = w.untimedSince.Format("2006/01/02 15:04:05") + " " + line
					changed = true
				}
				if _, err := writer.WriteString(line); err != nil {
					return err
				}
			} else {
				changed = true
			}
		}
		if readErr == io.EOF {
			break
		}
		if readErr != nil {
			return readErr
		}
	}
	if !changed {
		return nil
	}
	if err := writer.Flush(); err != nil {
		return err
	}
	if err := tmp.Sync(); err != nil {
		return err
	}
	// 新句柄也用 O_APPEND，后续日志始终追加到保留下来的内容之后。
	appendFile, err := os.OpenFile(tmpPath, os.O_WRONLY|os.O_APPEND, 0)
	if err != nil {
		return err
	}
	if err := os.Rename(tmpPath, w.path); err != nil {
		appendFile.Close()
		return err
	}
	oldFile := w.file
	w.file = appendFile
	oldFile.Close()
	return nil
}

func (w *retainedLogWriter) Close() error {
	w.closeOnce.Do(func() {
		close(w.stop)
		<-w.done
		w.mu.Lock()
		defer w.mu.Unlock()
		w.closed = true
		w.closeErr = w.file.Close()
	})
	return w.closeErr
}

// 后台 debug 的控制台输出也加上时间戳并通过统一 writer 写入。
func consolePrintf(format string, args ...interface{}) {
	if runtimeLogger != nil && runtimeLogger.debug && os.Getenv("CFNAT_DAEMONIZED") == "1" {
		runtimeLogger.logger.Printf(format, args...)
		return
	}
	fmt.Printf(format, args...)
}

func consolePrintln(args ...interface{}) {
	if runtimeLogger != nil && runtimeLogger.debug && os.Getenv("CFNAT_DAEMONIZED") == "1" {
		runtimeLogger.logger.Println(args...)
		return
	}
	fmt.Println(args...)
}

func initRuntimeLogger(logFilePath string, debug bool) (io.Closer, error) {
	logFilePath = strings.TrimSpace(logFilePath)
	if logFilePath == "" {
		return nil, nil
	}

	file, err := newRetainedLogWriter(logFilePath)
	if err != nil {
		return nil, err
	}

	runtimeLogger = &RuntimeLogger{
		debug:  debug,
		logger: log.New(file, "", log.LstdFlags),
	}

	if debug {
		// 后台标准输出指向空设备，所有文件日志均通过保留期限 writer 写入。
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

// ReplaceCandidates 更新排序但保留当前转发 IP，并同步其索引。
func (m *IPManager) ReplaceCandidates(ips []string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ipAddresses = append([]string(nil), ips...)
	m.currentIndex = -1
	for i, ip := range m.ipAddresses {
		if ip == m.currentIP {
			m.currentIndex = i
			break
		}
	}
	if m.currentIP != "" && m.currentIndex < 0 {
		m.currentIndex = len(m.ipAddresses)
		m.ipAddresses = append(m.ipAddresses, m.currentIP)
	}
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

// 只在测量期间当前 IP 未被别的协程改变时切换。
func (m *IPManager) SetCurrentIPIfUnchanged(oldIP, newIP string) (bool, int, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.currentIP != oldIP {
		return false, -1, false
	}
	for i, ip := range m.ipAddresses {
		if ip == newIP {
			changed := oldIP != newIP
			m.currentIP, m.currentIndex, m.allIPsChecked = newIP, i, false
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

	for offset := 0; offset < len(ips); offset++ {
		i := (startIndex + offset) % len(ips)
		ip := ips[i]
		if ip == currentIP {
			continue
		}

		if checkValidIP(ip, port, useTLS, domain, code) {
			_, index, found := m.SetCurrentIPIfUnchanged(currentIP, ip)
			if !found {
				// 列表或当前 IP 已被另一协程修改，下一轮重新检查。
				return m.GetCurrentIP() != ""
			}
			auditLogf("切换到新的有效 IP: %s 更新 IP 索引: %d", ip, index)
			return true
		}
	}

	m.mu.Lock()
	if m.currentIP != currentIP {
		m.mu.Unlock()
		return true
	}
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
	enabled      bool
	token        string
	zoneID       string
	recordID     string
	recordName   string
	proxied      bool
	ttl          int
	client       *http.Client
	mu           sync.Mutex
	lastIP       string
	recordLoaded bool
}

// CloudflareDNSGroup 为每个域名维护独立记录 ID 和更新缓存。
// 多域名模式使用健康检测后按延迟排序的独立分配列表。
type CloudflareDNSGroup struct {
	updaters       []*CloudflareDNSUpdater
	manager        *IPManager
	multi          bool
	mu             sync.Mutex
	refreshMu      sync.Mutex
	health         map[string]ddnsHealth
	rescan         func(context.Context) []string
	candidateLimit int
	probe          func(string) (time.Duration, bool)
}

func newCloudflareDNSGroup(enabled bool, token, zoneID, recordID, recordName, namesCSV, idsCSV string, proxied bool, ttl int, manager *IPManager) (*CloudflareDNSGroup, error) {
	g := &CloudflareDNSGroup{manager: manager, multi: strings.TrimSpace(namesCSV) != ""}
	if !enabled {
		return g, nil
	}
	if strings.TrimSpace(token) == "" || strings.TrimSpace(zoneID) == "" {
		return nil, fmt.Errorf("启用 DDNS 必须提供 cf-token 和 cf-zone-id")
	}
	names := []string{recordName}
	ids := []string{recordID}
	if g.multi {
		names = strings.Split(namesCSV, ",")
		ids = make([]string, len(names))
		if strings.TrimSpace(recordID) != "" {
			return nil, fmt.Errorf("多域名模式请使用 cf-record-ids，不能使用 cf-record-id")
		}
		if strings.TrimSpace(idsCSV) != "" {
			ids = strings.Split(idsCSV, ",")
			if len(ids) != len(names) {
				return nil, fmt.Errorf("cf-record-ids 数量必须与 cf-record-names 一致，可用空项自动查询")
			}
		}
	} else if strings.TrimSpace(idsCSV) != "" {
		return nil, fmt.Errorf("cf-record-ids 必须配合 cf-record-names 使用")
	}
	seen := make(map[string]bool)
	for i, name := range names {
		name = strings.ToLower(strings.TrimSuffix(strings.TrimSpace(name), "."))
		if name == "" || seen[name] {
			return nil, fmt.Errorf("第 %d 个域名为空或重复: %q", i+1, name)
		}
		seen[name] = true
		g.updaters = append(g.updaters, NewCloudflareDNSUpdater(true, token, zoneID, ids[i], name, proxied, ttl))
	}
	return g, nil
}

func (g *CloudflareDNSGroup) Enabled() bool { return g != nil && len(g.updaters) > 0 }

// UpdateIfChanged 仅用于单域名初始化和故障切换。
// 多域名更新统一由定时检测按延迟差值决定，避免其它路径绕过阈值。
func (g *CloudflareDNSGroup) UpdateIfChanged(currentIP string) error {
	if !g.Enabled() || g.multi {
		return nil
	}
	g.mu.Lock()
	defer g.mu.Unlock()
	return g.updaters[0].UpdateIfChanged(currentIP)
}

type ddnsHealth struct {
	failures int
	latency  time.Duration
	known    bool
}

// loadCurrentIP 从 Cloudflare 读取域名现有记录，避免重启后把未知旧 IP 当作空记录覆盖。
func (u *CloudflareDNSUpdater) loadCurrentIP(ctx context.Context) error {
	u.mu.Lock()
	defer u.mu.Unlock()
	return u.loadCurrentIPLocked(ctx)
}

func (u *CloudflareDNSUpdater) loadCurrentIPLocked(ctx context.Context) error {
	if u.recordLoaded {
		return nil
	}
	if u.recordID == "" {
		return u.findRecordIDLocked()
	}
	apiURL := fmt.Sprintf("https://api.cloudflare.com/client/v4/zones/%s/dns_records/%s", u.zoneID, u.recordID)
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, apiURL, nil)
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", "Bearer "+u.token)
	resp, err := u.client.Do(req)
	if err != nil {
		return fmt.Errorf("读取 Cloudflare AAAA 记录 %s 失败: %w", u.recordName, err)
	}
	defer resp.Body.Close()
	var payload cloudflareDNSRecordResponse
	if err := json.NewDecoder(resp.Body).Decode(&payload); err != nil {
		return fmt.Errorf("解析 Cloudflare AAAA 记录 %s 失败: %w", u.recordName, err)
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 || !payload.Success {
		return fmt.Errorf("读取 Cloudflare AAAA 记录 %s 失败，HTTP %d: %s", u.recordName, resp.StatusCode, formatCloudflareErrors(payload.Errors))
	}
	return u.setRecordContentLocked(payload.Result)
}

func (u *CloudflareDNSUpdater) setRecordContentLocked(record cloudflareDNSRecord) error {
	if record.ID == "" || record.Type != "AAAA" || !strings.EqualFold(strings.TrimSuffix(record.Name, "."), u.recordName) || (record.ID != "" && record.ID != u.recordID) {
		return fmt.Errorf("Cloudflare 记录 %s 的 ID、类型或域名不匹配", u.recordName)
	}
	addr, err := netip.ParseAddr(record.Content)
	if err != nil || !addr.Is6() {
		return fmt.Errorf("Cloudflare 记录 %s 的现有 IPv6 无效: %q", u.recordName, record.Content)
	}
	u.lastIP = addr.String()
	u.recordLoaded = true
	return nil
}

func (u *CloudflareDNSUpdater) currentIP() string {
	u.mu.Lock()
	defer u.mu.Unlock()
	return u.lastIP
}

func (u *CloudflareDNSUpdater) currentRecord() (string, bool) {
	u.mu.Lock()
	defer u.mu.Unlock()
	return u.lastIP, u.recordLoaded
}

// probeIPs 检测全部地址，concurrency 仅限制并发数，不限制检测范围。
func (g *CloudflareDNSGroup) probeIPs(ctx context.Context, ips []string, concurrency int) map[string]ddnsHealth {
	if concurrency < 1 {
		concurrency = 1
	}
	observed := make(map[string]ddnsHealth)
	if g.probe == nil {
		return observed
	}
	var mu sync.Mutex
	var wg sync.WaitGroup
	sem := make(chan struct{}, concurrency)
	seen := make(map[string]bool)
loop:
	for _, ip := range ips {
		if ip == "" || seen[ip] {
			continue
		}
		seen[ip] = true
		if ctx.Err() != nil {
			break
		}
		select {
		case <-ctx.Done():
			break loop
		case sem <- struct{}{}:
		}
		wg.Add(1)
		go func(ip string) {
			defer wg.Done()
			defer func() { <-sem }()
			elapsed, ok := g.probe(ip)
			mu.Lock()
			observed[ip] = ddnsHealth{latency: elapsed, known: ok}
			mu.Unlock()
		}(ip)
	}
	wg.Wait()
	return observed
}

// 本轮成功项才能参与排名；旧域名 IP 保留连续两轮失败的容错。
func (g *CloudflareDNSGroup) applyHealth(observations map[string]ddnsHealth) {
	if g.health == nil {
		g.health = make(map[string]ddnsHealth)
	}
	for ip, obs := range observations {
		state := g.health[ip]
		if obs.known {
			state = ddnsHealth{latency: obs.latency, known: true}
		} else if state.failures < 2 {
			state.failures++
		}
		g.health[ip] = state
	}
}

func rankAvailableIPs(ips []string, observations map[string]ddnsHealth) []string {
	var ranked []string
	seen := make(map[string]bool)
	for _, ip := range ips {
		if !seen[ip] && observations[ip].known {
			seen[ip] = true
			ranked = append(ranked, ip)
		}
	}
	sort.SliceStable(ranked, func(i, j int) bool {
		return observations[ranked[i]].latency < observations[ranked[j]].latency
	})
	return ranked
}

// 按域名配置顺序，从最快的未占用候选开始选择。
// 未达到延迟改善阈值的域名保留原记录，并保留其 IP 的占用关系。
func (g *CloudflareDNSGroup) updateRanked(ctx context.Context, ranked []string, observations map[string]ddnsHealth, threshold time.Duration) {
	if !g.Enabled() {
		return
	}
	if threshold < 0 {
		threshold = 0
	}
	g.mu.Lock()
	defer g.mu.Unlock()
	occupied := make(map[string]int)
	for _, updater := range g.updaters {
		if ip := updater.currentIP(); ip != "" {
			occupied[ip]++
		}
	}
	for _, updater := range g.updaters {
		if ctx.Err() != nil {
			return
		}
		oldIP, loaded := updater.currentRecord()
		if !loaded && oldIP == "" {
			continue
		}
		oldObs, measured := observations[oldIP]
		// 其它协程可能刚完成故障切换，未测量的新旧基准留待下一轮。
		if oldIP != "" && (!measured || (!oldObs.known && g.health[oldIP].failures < 2)) {
			auditLogf("DDNS 保留 %s -> %s：本轮无可比较延迟或尚未连续失败两轮", updater.recordName, oldIP)
			continue
		}
		chosen := ""
		for _, ip := range ranked {
			if ip == oldIP || occupied[ip] > 0 || !observations[ip].known {
				continue
			}
			if oldIP != "" && oldObs.known && oldObs.latency-observations[ip].latency <= threshold {
				continue
			}
			chosen = ip
			break
		}
		if chosen == "" {
			auditLogf("DDNS 保留 %s -> %s：没有未占用且改善超过 %d ms 的候选 IP", updater.recordName, oldIP, threshold.Milliseconds())
			continue
		}
		if err := updater.UpdateIfChanged(chosen); err != nil {
			auditLogf("DDNS 更新 %s 失败，保留原分配并等待下轮重试: %v", updater.recordName, err)
			continue
		}
		if oldIP != "" {
			occupied[oldIP]--
		}
		occupied[chosen]++
		if oldIP != "" && oldObs.known {
			auditLogf("DDNS 延迟优化 %s: %s -> %s，%d ms -> %d ms，改善 %d ms，阈值 %d ms", updater.recordName, oldIP, chosen, oldObs.latency.Milliseconds(), observations[chosen].latency.Milliseconds(), (oldObs.latency - observations[chosen].latency).Milliseconds(), threshold.Milliseconds())
		} else {
			auditLogf("DDNS 初始化或故障替换 %s: %s -> %s", updater.recordName, oldIP, chosen)
		}
	}
}

// refresh 为转发选路和 DDNS 共用同一轮测量结果。
func (g *CloudflareDNSGroup) refresh(ctx context.Context, concurrency int, threshold time.Duration) ([]string, map[string]ddnsHealth) {
	g.refreshMu.Lock()
	defer g.refreshMu.Unlock()
	ips := g.manager.GetIPAddresses()
	probeList := append([]string(nil), ips...)
	probeList = append(probeList, g.manager.GetCurrentIP())
	for _, updater := range g.updaters {
		if err := updater.loadCurrentIP(ctx); err != nil {
			auditLogf("读取 %s 的当前 AAAA 记录失败，本轮暂不更新该域名: %v", updater.recordName, err)
		}
		probeList = append(probeList, updater.currentIP())
	}
	observations := g.probeIPs(ctx, probeList, concurrency)
	if ctx.Err() != nil {
		return nil, observations
	}
	g.applyHealth(observations)
	ranked := rankAvailableIPs(ips, observations)
	auditLogf("定时选路全量检测：候选 %d 个，本轮可用 %d 个，按延迟排序 %v", len(ips), len(ranked), ranked)
	// 先处理已有候选，避免随机补充耗时阻塞本轮域名更新。
	g.updateRanked(ctx, ranked, observations, threshold)
	if len(ranked) < 10 && g.rescan != nil {
		auditLogf("本轮可用 IP 为 %d 个，少于 10 个，启动随机筛选补充，目标候选数 %d", len(ranked), g.candidateLimit)
		fresh := g.rescan(ctx)
		if ctx.Err() != nil {
			return nil, observations
		}
		seen := make(map[string]bool)
		for _, ip := range ips {
			seen[ip] = true
		}
		var added, unmeasured []string
		for _, ip := range fresh {
			if ip == "" || seen[ip] {
				continue
			}
			seen[ip] = true
			added = append(added, ip)
			if _, ok := observations[ip]; !ok {
				unmeasured = append(unmeasured, ip)
			}
		}
		newObservations := g.probeIPs(ctx, unmeasured, concurrency)
		if ctx.Err() != nil {
			return nil, observations
		}
		// 已测量项在同一轮中不能被重复计为两次失败。
		g.applyHealth(newObservations)
		for ip, obs := range newObservations {
			observations[ip] = obs
		}
		ips = append(ips, added...)
		ranked = rankAvailableIPs(ips, observations)
		auditLogf("随机补充完成：本轮可用 %d 个，按延迟排序 %v", len(ranked), ranked)
		g.updateRanked(ctx, ranked, observations, threshold)
	}
	// 保留速度最快的候选，空位保留暂时失败项以便下轮复测，防止列表无限增长。
	ordered := append([]string(nil), ranked...)
	seen := make(map[string]bool)
	for _, ip := range ordered {
		seen[ip] = true
	}
	for _, ip := range ips {
		if !seen[ip] {
			ordered = append(ordered, ip)
			seen[ip] = true
		}
	}
	if g.candidateLimit > 0 && len(ordered) > g.candidateLimit {
		ordered = ordered[:g.candidateLimit]
	}
	g.manager.ReplaceCandidates(ordered)
	// 只保留下轮仍会检测的健康状态，避免反复补充后持续占用内存。
	retained := make(map[string]bool)
	for _, ip := range g.manager.GetIPAddresses() {
		retained[ip] = true
	}
	retained[g.manager.GetCurrentIP()] = true
	for _, updater := range g.updaters {
		retained[updater.currentIP()] = true
	}
	for ip := range g.health {
		if !retained[ip] {
			delete(g.health, ip)
		}
	}
	return ranked, observations
}

// 关闭定时选路时，多域名仍每 60 秒刷新一次。
func (g *CloudflareDNSGroup) run(ctx context.Context, interval time.Duration, concurrency int, threshold time.Duration) {
	if !g.Enabled() || !g.multi {
		return
	}
	if interval > 0 {
		<-ctx.Done()
		return
	}
	g.refresh(ctx, concurrency, threshold)
	ticker := time.NewTicker(60 * time.Second)
	defer ticker.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			g.refresh(ctx, concurrency, threshold)
		}
	}
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

	if err := u.loadCurrentIPLocked(context.Background()); err != nil {
		return err
	}
	if u.lastIP == ip {
		auditLogf("Cloudflare AAAA 记录未更新: %s 仍为 %s", u.recordName, ip)
		return nil
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
	u.recordLoaded = true
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

	if len(cfResp.Result) != 1 {
		return fmt.Errorf("域名 %s 存在多个 AAAA 记录，请显式指定对应的记录 ID", u.recordName)
	}
	u.recordID = cfResp.Result[0].ID
	if err := u.setRecordContentLocked(cfResp.Result[0]); err != nil {
		return err
	}
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

func daemonize() (int, error) {
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

	// 子进程通过日志 writer 管理文件，禁止 stdout/stderr 绕过清理锁直接写文件。
	outputFile, err := os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	if err != nil {
		return 0, fmt.Errorf("打开后台输出重定向失败: %w", err)
	}
	defer outputFile.Close()

	env := append(os.Environ(), "CFNAT_DAEMONIZED=1")
	attr := &os.ProcAttr{
		Dir:   workDir,
		Env:   env,
		Files: []*os.File{stdinFile, outputFile, outputFile},
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
	num := flag.Int("num", 5, "定时选路检测全部候选 IP 时的最大并发数")
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
	cfRecordNames := flag.String("cf-record-names", "", "多个 AAAA 域名，用逗号分隔，按配置顺序选择满足延迟改善阈值的未占用 IP；优先于 cf-record-name")
	cfRecordIDs := flag.String("cf-record-ids", "", "可选：与 cf-record-names 顺序对应的记录 ID，逗号分隔，空项自动查询")
	cfProxied := flag.Bool("cf-proxied", false, "Cloudflare DNS 记录是否开启代理")
	cfTTL := flag.Int("cf-ttl", 1, "Cloudflare DNS TTL，1 表示自动")
	logFile := flag.String("log-file", "cfnat.log", "日志文件路径，自动保留最近 24 小时；为空表示不写日志文件")
	debugLog := flag.Bool("debug", false, "debug 模式：将全部 log 输出同时写入日志文件")
	error1034Enabled := flag.Bool("error1034-enable", false, "启用指定 URL 的 Cloudflare error code: 1034 验证")
	error1034URL := flag.String("error1034-url", "", "1034 验证 URL，例如 https://deed.cloudmeai.de5.net:2053/；连接到每个待测 IP")
	daemonMode := flag.Bool("d", false, "后台运行模式；父进程启动后台子进程后退出")

	flag.Parse()

	if *ipCount <= 0 || *maxThreads <= 0 {
		log.Fatal("ipnum 和 task 必须大于 0")
	}
	if *error1034Enabled {
		parsed, err := url.Parse(strings.TrimSpace(*error1034URL))
		if err != nil || parsed.Scheme != "https" || parsed.Hostname() == "" || parsed.User != nil {
			log.Fatal("HTTP/2 1034 验证要求 error1034-url 为有效的 https:// URL")
		}
		checkPort := parsed.Port()
		if checkPort == "" {
			checkPort = "443"
		}
		error1034Check = &error1034Validator{url: parsed.String(), port: checkPort}
	}

	if *daemonMode && os.Getenv("CFNAT_DAEMONIZED") != "1" {
		pid, err := daemonize()
		if err != nil {
			log.Fatalf("后台运行启动失败: %v", err)
		}
		consolePrintf("已后台运行，PID: %d，日志文件: %s\n", pid, *logFile)
		return
	}

	logHandle, err := initRuntimeLogger(*logFile, *debugLog)
	if err != nil {
		log.Fatalf("无法打开日志文件 %s: %v", *logFile, err)
	}
	if logHandle != nil {
		defer logHandle.Close()
		auditLogf("日志文件已启用: %s，保留最近 24 小时，每 10 分钟清理，debug=%v，daemon=%v", *logFile, *debugLog, os.Getenv("CFNAT_DAEMONIZED") == "1")
	}
	if *error1034Enabled {
		auditLogf("1034 HTTP/2 验证已启用：URL=%s", error1034Check.url)
	}

	ipManager := NewIPManager()
	cfUpdater, err := newCloudflareDNSGroup(*cfEnable, *cfToken, *cfZoneID, *cfRecordID, *cfRecordName, *cfRecordNames, *cfRecordIDs, *cfProxied, *cfTTL, ipManager)
	if err != nil {
		log.Fatalf("Cloudflare DDNS 配置错误: %v", err)
	}
	if cfUpdater.Enabled() {
		if *ipsType != "6" {
			log.Fatal("Cloudflare AAAA 更新需要 -ips 6")
		}
		for i, updater := range cfUpdater.updaters {
			auditLogf("Cloudflare AAAA 自动更新已启用：域名[%d]=%s，多域名候选映射=%v", i+1, updater.recordName, cfUpdater.multi)
		}
	}

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
			consolePrintln("无效的IP类型。请使用 '4' 或 '6'")
			return
		}

		var content string

		if _, err = os.Stat(filename); os.IsNotExist(err) {
			consolePrintf("文件 %s 不存在，正在从 URL %s 下载数据\n", filename, url)
			content, err = getURLContent(url)
			if err != nil {
				consolePrintln("获取URL内容出错:", err)
				return
			}
			err = saveToFile(filename, content)
			if err != nil {
				consolePrintln("保存文件出错:", err)
				return
			}
		} else {
			content, err = getFileContent(filename)
			if err != nil {
				consolePrintln("读取本地文件出错:", err)
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
				consolePrintln("读取IP出错:", err)
				return
			}
		}

		var nextBatch func() []string
		if *random {
			nextBatch = func() []string {
				if *ipsType == "6" {
					return getRandomIPv6s(parseIPList(content))
				}
				return getRandomIPv4s(parseIPList(content))
			}
		}
		collect := func(pool []string) []result {
			return collectCandidateIPs(context.Background(), pool, nextBatch, func(batch []string) []result {
				return scanIPs(context.Background(), batch, locationMap, *maxThreads)
			}, *ipCount, *coloFilter)
		}
		results := collect(ipList)

		if len(results) == 0 {
			consolePrintln("未发现有效IP")
			time.Sleep(3 * time.Second)
			continue
		}

		consolePrintln("IP 地址 | 数据中心 | 地区 | 城市 | 延迟")
		for _, r := range results {
			consolePrintf("%s | %s | %s | %s | %s\n", r.ip, r.dataCenter, r.region, r.city, r.latency)
		}

		consolePrintf("成功提取 %d 个有效IP，耗时 %d秒\n", len(results), time.Since(startTime)/time.Second)

		var ips []string
		for _, r := range results {
			ips = append(ips, r.ip)
		}
		ipManager.SetIPAddresses(ips)
		cfUpdater.health = make(map[string]ddnsHealth)
		cfUpdater.candidateLimit = max(*ipCount, 10)
		cfUpdater.probe = func(ip string) (time.Duration, bool) {
			elapsed, ok := measureIPDelay(ip, *port, time.Duration(*Delay)*time.Millisecond)
			if !ok || elapsed > time.Duration(*Delay)*time.Millisecond {
				return elapsed, false
			}
			return elapsed, checkValidIP(ip, *port, *useTLS, *domain, *code)
		}
		cfUpdater.rescan = func(ctx context.Context) []string {
			// 候选不足时始终随机抽样，包括启动时使用 -random=false 的情况。
			generate := func() []string {
				if *ipsType == "6" {
					return getRandomIPv6s(parseIPList(content))
				}
				return getRandomIPv4s(parseIPList(content))
			}
			fresh := collectCandidateIPs(ctx, generate(), generate, func(batch []string) []result {
				return scanIPs(ctx, batch, locationMap, *maxThreads)
			}, cfUpdater.candidateLimit, *coloFilter)
			replenished := make([]string, 0, len(fresh))
			for _, r := range fresh {
				replenished = append(replenished, r.ip)
			}
			return replenished
		}

		currentIP, currentIndex := selectValidIP(ipManager, *useTLS, *port, *domain, *code)
		if currentIP == "" {
			log.Printf("没有有效的 IP 可用")
			continue
		}
		ipManager.SetCurrentIPWithIndex(currentIP, currentIndex)
		logSelectedIPList(results, currentIP, currentIndex)
		if !cfUpdater.multi {
			if err := cfUpdater.UpdateIfChanged(currentIP); err != nil {
				auditLogf("更新 Cloudflare AAAA 记录失败: %v", err)
			}
		}

		ctx, cancel := context.WithCancel(context.Background())
		done := make(chan bool)

		var loopWG sync.WaitGroup
		loopWG.Add(4)
		go func() {
			defer loopWG.Done()
			cfUpdater.run(ctx, time.Duration(*routeInterval)*time.Second, *num, time.Duration(*routeThreshold)*time.Millisecond)
		}()

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
		log.Println("主函数将退出当前循环，因为所有 IP 都已用尽")
	}
}

// loadLocations 加载位置信息，使用函数封装确保 defer 正确执行
func loadLocations() ([]location, error) {
	var locations []location

	if _, err := os.Stat("locations.json"); os.IsNotExist(err) {
		consolePrintln("本地 locations.json 不存在\n正在从 https://www.baipiao.eu.org/cloudflare/locations 下载 locations.json")
		resp, err := (&http.Client{Timeout: 15 * time.Second}).Get("https://www.baipiao.eu.org/cloudflare/locations")
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

// collectCandidateIPs 按轮次累积通过机房过滤的不同 IP，达到目标数量后按延迟排序。
// 随机模式持续补充；固定列表用尽时返回实际数量。
func collectCandidateIPs(ctx context.Context, pool []string, nextBatch func() []string, scan func([]string) []result, target int, coloFilter string) []result {
	if target <= 0 {
		return nil
	}
	var results []result
	seen := make(map[string]struct{})
	filters := strings.Split(coloFilter, ",")
	for round := 1; ctx.Err() == nil; round++ {
		batch := make([]string, 0, len(pool))
		batchSeen := make(map[string]struct{}, len(pool))
		for _, ip := range pool {
			if _, ok := seen[ip]; ok {
				continue
			}
			if _, ok := batchSeen[ip]; ok {
				continue
			}
			batchSeen[ip] = struct{}{}
			batch = append(batch, ip)
		}
		if len(batch) == 0 {
			break
		}
		for _, r := range scan(batch) {
			if coloFilter != "" {
				matched := false
				for _, filter := range filters {
					if strings.EqualFold(r.dataCenter, strings.TrimSpace(filter)) {
						matched = true
						break
					}
				}
				if !matched {
					continue
				}
			}
			if _, ok := seen[r.ip]; ok {
				continue
			}
			seen[r.ip] = struct{}{}
			results = append(results, r)
		}
		consolePrintf("第 %d 轮初筛完成：已累计 %d 个候选 IP，目标 %d 个\n", round, len(results), target)
		if len(results) >= target || nextBatch == nil {
			break
		}
		select {
		case <-ctx.Done():
			return nil
		case <-time.After(3 * time.Second):
		}
		pool = nextBatch()
	}
	sort.Slice(results, func(i, j int) bool {
		return results[i].tcpDuration < results[j].tcpDuration
	})
	if len(results) > target {
		results = results[:target]
	}
	return results
}

// scanIPs 扫描 IP 列表并返回结果
func scanIPs(ctx context.Context, ipList []string, locationMap map[string]location, maxThreads int) []result {
	var wg sync.WaitGroup
	var mu sync.Mutex
	var results []result

	thread := make(chan struct{}, maxThreads)

	var count int32
	total := len(ipList)

scanLoop:
	for _, ip := range ipList {
		if ctx.Err() != nil {
			break
		}
		select {
		case <-ctx.Done():
			break scanLoop
		case thread <- struct{}{}:
		}
		wg.Add(1)
		go func(ipAddr string) {
			defer func() {
				<-thread
				wg.Done()
				current := atomic.AddInt32(&count, 1)
				percentage := float64(current) / float64(total) * 100
				consolePrintf("已完成: %d 总数: %d 已完成: %.2f%%\r", current, total, percentage)
				if int(current) == total {
					consolePrintf("已完成: %d 总数: %d 已完成: %.2f%%\n", current, total, percentage)
				}
			}()

			dialer := &net.Dialer{
				Timeout:   timeout,
				KeepAlive: 0,
			}
			start := time.Now()
			conn, err := dialer.DialContext(ctx, "tcp", net.JoinHostPort(ipAddr, "80"))
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
				consolePrintf("发现有效IP %s 位置信息 %s 延迟 %d 毫秒\n", ipAddr, loc.City, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, loc.Region, loc.City, fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			} else {
				consolePrintf("发现有效IP %s 位置信息未知 延迟 %d 毫秒\n", ipAddr, tcpDuration.Milliseconds())
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
	resp, err := (&http.Client{Timeout: 15 * time.Second}).Get(url)
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

// 从每个 IPv4 CIDR 中随机提取一个地址，支持 /24 及其他掩码。
func getRandomIPv4s(ipList []string) []string {
	var randomIPs []string
	for _, subnet := range ipList {
		subnet = strings.TrimSpace(subnet)
		if !strings.Contains(subnet, "/") {
			addr, err := netip.ParseAddr(subnet)
			if err == nil && addr.Is4() {
				subnet = netip.PrefixFrom(addr, 24).Masked().String()
			}
		}
		prefix, err := netip.ParsePrefix(subnet)
		if err != nil || !prefix.Addr().Is4() {
			continue
		}
		prefix = prefix.Masked()
		bytes := prefix.Addr().As4()
		bits := prefix.Bits()
		for bit := bits; bit < 32; bit++ {
			if nextRandomIntn(2) == 1 {
				bytes[bit/8] |= 1 << uint(7-bit%8)
			}
		}
		randomIPs = append(randomIPs, netip.AddrFrom4(bytes).String())
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

// 如果掩码 < 55，则最多选取 128 个不同的 /55，每个子网随机取一个 IPv6（/48 恰好 128 个）
// 如果掩码 >= 55，则从当前 CIDR 中随机提取一个 IPv6
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

		if bits < 55 {
			count := uint64(1) << uint(55-bits)
			step := uint64(1)
			if count > 128 {
				step = count / 128
				count = 128
			}

			for i := uint64(0); i < count; i++ {
				p55 := makeSubPrefix(prefix, 55, i*step)
				randomIPs = append(randomIPs, randomIPv6InPrefix(p55))
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
			ones, width := ipNet.Mask.Size()
			if width-ones > 16 {
				return nil, fmt.Errorf("网段 %s 含超过 65536 个 IP，无法完整展开；请使用 -random=true", line)
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
	targetURL := fmt.Sprintf("http://%s", domain)
	if useTLS {
		targetURL = fmt.Sprintf("https://%s", domain)
	}

	// 每个探测独立创建 Transport，避免随机补充 IP 使客户端缓存无限增长。
	transport := &http.Transport{
		TLSClientConfig:   &tls.Config{InsecureSkipVerify: true},
		DisableKeepAlives: true,
		DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
			dialer := &net.Dialer{Timeout: 2 * time.Second}
			return dialer.DialContext(ctx, network, net.JoinHostPort(ip, fmt.Sprintf("%d", port)))
		},
	}
	defer transport.CloseIdleConnections()
	client := &http.Client{Timeout: 2 * time.Second, Transport: transport}

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

	return error1034Check.valid(ip)
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

func statusCheck(ctx context.Context, useTLS bool, port int, done chan bool, domain string, code int, delay time.Duration, ipManager *IPManager, cfUpdater *CloudflareDNSGroup) {
	interval := 2 * time.Second
	if delay > interval {
		interval = delay
	}

	ticker := time.NewTicker(interval)
	defer ticker.Stop()

	failCount := 0
	wasUnhealthy := false
	lastLoggedIP := ""
	lastCheckedIP := ""
	auditLogf("状态检查已启动：间隔=%d ms，失败阈值=2 次", interval.Milliseconds())

	for {
		select {
		case <-ctx.Done():
			auditLogln("状态检查收到退出信号")
			return
		case <-ticker.C:
			currentIP := ipManager.GetCurrentIP()
			if currentIP != lastCheckedIP {
				failCount, wasUnhealthy = 0, false
				lastCheckedIP = currentIP
			}
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

			if ipManager.GetCurrentIP() != currentIP {
				// 定时选路在检查期间已切换，不累计旧 IP 的失败次数。
				failCount, wasUnhealthy = 0, false
				continue
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

// periodicRouteSelector 全量检测候选，共用测量结果进行 DDNS 优化和转发选路。
func periodicRouteSelector(ctx context.Context, interval time.Duration, num int, port int, delay time.Duration, routeThreshold time.Duration, ipManager *IPManager, cfUpdater *CloudflareDNSGroup) {
	if interval <= 0 {
		auditLogln("定时选路已关闭")
		<-ctx.Done()
		return
	}
	if routeThreshold < 0 {
		routeThreshold = 0
	}
	runSelect := func(reason string) {
		auditLogf("定时选路开始：原因=%s，并发数=%d，目标端口=%d，有效延迟=%d ms，优化阈值=%d ms", reason, num, port, delay.Milliseconds(), routeThreshold.Milliseconds())
		ranked, observations := cfUpdater.refresh(ctx, num, routeThreshold)
		if ctx.Err() != nil || len(ranked) == 0 {
			return
		}
		currentIP := ipManager.GetCurrentIP()
		current, measured := observations[currentIP]
		if currentIP != "" && !measured {
			return
		}
		bestIP := ranked[0]
		best := observations[bestIP]
		if bestIP == currentIP {
			return
		}
		if currentIP != "" && current.known && current.latency-best.latency <= routeThreshold {
			auditLogf("定时选路保持当前 IP %s：最佳候选 %s 改善 %d ms，未超过阈值 %d ms", currentIP, bestIP, (current.latency - best.latency).Milliseconds(), routeThreshold.Milliseconds())
			return
		}
		changed, index, found := ipManager.SetCurrentIPIfUnchanged(currentIP, bestIP)
		if found && changed {
			auditLogf("定时选路更新转发 IP: %s -> %s，延迟 %d ms，索引 %d", currentIP, bestIP, best.latency.Milliseconds(), index)
		}
		// DDNS 已由 refresh 按每个域名自己的延迟基准更新，不能再用转发 IP 覆盖。
	}
	runSelect("startup")
	ticker := time.NewTicker(interval)
	defer ticker.Stop()
	for {
		select {
		case <-ctx.Done():
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
		if tcp, ok := src.(*net.TCPConn); ok {
			tcp.CloseWrite()
		}
	}()

	go func() {
		defer wg.Done()
		_, _ = io.Copy(dst, src)
		if tcp, ok := dst.(*net.TCPConn); ok {
			tcp.CloseWrite()
		}
	}()

	wg.Wait()
	closeBoth()
}
