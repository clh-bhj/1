# -*- coding: utf-8 -*-
"""
真果·鉴 · 壳端 py 源（TVBox / 海阔视界 / PeekPro 通用）
=================================================================
对接本机跑着的「真果·鉴 Node 服务」，默认 http://127.0.0.1:8992。

【服务地址已内置】就是下面 SERVER_URL 那一行，进源即用，不用手填。
  同机（壳和服务在一台设备）：保持 127.0.0.1 就行
  分机（服务在电脑/盒子/另一台手机）：改成 http://192.168.x.x:8992

【这个源能干什么】
  搜索        —— 关键词跨站聚合（壳的搜索框直接用）
  站源分类    —— 每个站源一个入口，点进去是该站的短剧/影视列表，可按分类筛选、翻页
  详情        —— 剧集信息 + 全集列表
  播放        —— 直接取 m3u8/mp4 真实地址，服务端会先把死线路剔掉
  服务自检    —— 一条链排查「服务没起来 / 哪个站源没数据」

依赖：纯标准库，无第三方包。
"""

import base64
import json
import socket
import threading
import urllib.error
import urllib.parse
import urllib.request

try:
    from base.spider import Spider as _BaseSpider
except Exception:
    _BaseSpider = object


# ==================================================================
# 配置区
# ==================================================================

# 内置服务地址：只写 协议://IP:端口，不要带路径
SERVER_URL = "http://127.0.0.1:8992"

# 服务前缀：真果鉴 Node 版接口都在 /api 下，这里留空即可
BASE_PATH = ""

# 每页条数
PAGE_SIZE = 30

# 请求超时（秒）
REQ_TIMEOUT = 25

# 自检分类的 type_id
DIAG_TID = "diag"

UA = ("Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36")


# ==================================================================
# 小工具
# ==================================================================

def _b64e(obj):
    return base64.urlsafe_b64encode(
        json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    ).decode("ascii").rstrip("=")


def _b64d(text):
    if not isinstance(text, str) or not text:
        return None
    s = text.strip()
    pad = "=" * (-len(s) % 4)
    try:
        raw = base64.urlsafe_b64decode((s + pad).encode("ascii"))
        obj = json.loads(raw.decode("utf-8"))
        return obj if isinstance(obj, dict) else None
    except Exception:
        return None


def _text(raw):
    if raw is None:
        return ""
    return str(raw).replace("\r", " ").replace("\n", " ").strip()


class Spider(_BaseSpider):
    def __init__(self):
        self.base = SERVER_URL.rstrip("/")
        self.origin = self.base
        self.extend_info = {}
        self._cats = {}
        self._lock = threading.Lock()

    # ---------------- 初始化 ----------------

    def init(self, extend=""):
        self.setExtendInfo(extend)
        try:
            self._get("/api/health", timeout=6)
        except Exception:
            pass
        return self

    def setExtendInfo(self, extend):
        self.extend_info = self._parse_extend(extend)

    def _parse_extend(self, extend):
        if not extend:
            return {}
        if isinstance(extend, dict):
            return extend
        try:
            obj = json.loads(extend)
            if isinstance(obj, dict):
                return obj
        except Exception:
            pass
        return {}

    def getName(self):
        return "真果·鉴"

    def isVideoFormat(self, url):
        return bool(url) and (".m3u8" in str(url) or ".mp4" in str(url))

    def manualVideoCheck(self):
        return False

    def destroy(self):
        return None

    # ---------------- HTTP ----------------

    def _url(self, path, params=None):
        base = (self.base or SERVER_URL).rstrip("/")
        if BASE_PATH:
            base += BASE_PATH
        url = base + path
        if params:
            qs = urllib.parse.urlencode({k: v for k, v in params.items() if v is not None and v != ""})
            if qs:
                url += ("&" if "?" in url else "?") + qs
        return url

    def _get(self, path, params=None, timeout=None):
        url = self._url(path, params)
        req = urllib.request.Request(url, headers={
            "User-Agent": UA,
            "Accept": "application/json,text/plain,*/*",
            "Accept-Encoding": "identity",
        })
        with urllib.request.urlopen(req, timeout=timeout or REQ_TIMEOUT) as resp:
            body = resp.read()
        txt = body.decode("utf-8", "replace").strip()
        return json.loads(txt) if txt else {}

    def _err_text(self, e):
        if isinstance(e, urllib.error.HTTPError):
            try:
                raw = e.read().decode("utf-8", "replace")
                obj = json.loads(raw)
                if isinstance(obj, dict) and obj.get("error"):
                    return _text(obj.get("error"))
            except Exception:
                pass
            return "服务返回 HTTP %s" % e.code
        if isinstance(e, socket.timeout):
            return "服务响应超时"
        msg = str(e)
        if "refused" in msg or "Errno 111" in msg or "timed out" in msg:
            return "服务没连上（%s）" % (self.base or SERVER_URL)
        return msg or "请求失败"

    # ---------------- 数据映射 ----------------

    def _vod(self, item):
        src = item.get("source") or ""
        pics = _text(item.get("pic"))
        if pics and not pics.startswith("http"):
            pics = ""
        return {
            "vod_id": _b64e({"t": "v", "s": src, "i": str(item.get("id") or "")}),
            "vod_name": _text(item.get("name")) or "未命名",
            "vod_pic": pics,
            "vod_remarks": _text(item.get("remarks")) or _text(item.get("typeName")),
            "vod_tag": "",
            "vod_year": _text(item.get("year")),
            "vod_area": _text(item.get("area")),
            "vod_douban_id": 0,
            "vod_content": "",
            "vod_play_from": "真果鉴",
            "vod_play_url": "",
        }

    def _note_vod(self, title, text, sub="点开看说明"):
        return {
            "vod_id": _b64e({"t": "none", "n": title, "msg": text}),
            "vod_name": title,
            "vod_pic": "",
            "vod_remarks": sub,
            "vod_tag": "",
            "vod_douban_id": 0,
            "vod_content": text,
            "vod_play_from": "真果鉴",
            "vod_play_url": "说明$" + _b64e({"t": "none"}),
        }

    # ---------------- 分类 ----------------

    def _sources(self):
        try:
            d = self._get("/api/sources", timeout=8)
            return d.get("sources") or []
        except Exception:
            return []

    def _source_cats(self, sid):
        with self._lock:
            if sid in self._cats:
                return self._cats[sid]
        cats = []
        try:
            d = self._get("/api/home", {"source": sid}, timeout=20)
            cats = d.get("categories") or []
        except Exception:
            cats = []
        with self._lock:
            self._cats[sid] = cats
        return cats

    def homeContent(self, filter=False):
        sources = self._sources()
        classes = [{"type_id": "agg", "type_name": "🔥 聚合首页"}]
        filters = {}
        ready = [s for s in sources if s.get("ready")]
        if not ready:
            classes.append({"type_id": DIAG_TID, "type_name": "🩺 服务自检"})
            return {"class": classes, "filters": filters}

        # 并行取各站分类，用来做筛选条
        threads = []
        for s in ready:
            t = threading.Thread(target=self._source_cats, args=(s.get("id"),))
            t.daemon = True
            t.start()
            threads.append(t)
        for t in threads:
            t.join(timeout=12)

        for s in ready:
            sid = s.get("id")
            classes.append({"type_id": "src:" + sid, "type_name": _text(s.get("name"))})
            cats = self._cats.get(sid) or []
            if cats:
                opts = [{"n": "全部", "v": ""}]
                for c in cats[:60]:
                    opts.append({"n": _text(c.get("name")), "v": str(c.get("id") or "")})
                filters["src:" + sid] = [{"key": "cat", "name": "分类", "value": opts}]

        classes.append({"type_id": DIAG_TID, "type_name": "🩺 服务自检"})
        return {"class": classes, "filters": filters}

    def homeVideoContent(self):
        try:
            d = self._get("/api/home", timeout=30)
            vods = [self._vod(it) for it in (d.get("list") or [])][:PAGE_SIZE]
        except Exception as e:
            vods = [self._note_vod("服务没连上", self._err_text(e) + "\n\n先把 Node 服务跑起来：node server.js")]
        if not vods:
            vods = [self._note_vod("暂无内容", "服务起来了，但这几个站源暂时没取到列表。\n点「🩺 服务自检」看看哪个站源有问题。")]
        return {"list": vods}

    def categoryContent(self, tid, pg="1", filter=False, extend=None):
        tid = _text(tid)
        try:
            page_no = max(1, int(pg))
        except Exception:
            page_no = 1
        ext = extend if isinstance(extend, dict) else {}

        if tid == DIAG_TID:
            return {"list": [self._diag_vod()], "page": 1, "pagecount": 1, "limit": 1, "total": 1}
        if tid == "agg":
            got = self.homeVideoContent()
            return {"list": got["list"], "page": 1, "pagecount": 1, "limit": PAGE_SIZE, "total": len(got["list"])}
        if tid.startswith("src:"):
            sid = tid[4:]
            cat = _text(ext.get("cat"))
            try:
                if cat:
                    d = self._get("/api/category", {"source": sid, "tid": cat, "page": page_no}, timeout=30)
                else:
                    d = self._get("/api/home", {"source": sid}, timeout=30)
            except Exception as e:
                return {"list": [self._note_vod("取不到这个站的内容", self._err_text(e))],
                        "page": page_no, "pagecount": 1, "limit": PAGE_SIZE, "total": 1}
            vods = [self._vod(it) for it in (d.get("list") or [])]
            if not vods:
                return {"list": [self._note_vod("这一页是空的", "换个分类或者翻回第一页试试。")],
                        "page": page_no, "pagecount": 1, "limit": PAGE_SIZE, "total": 1}
            has_more = d.get("hasMore")
            pagecount = page_no + 1 if has_more else page_no
            return {"list": vods, "page": page_no, "pagecount": pagecount,
                    "limit": PAGE_SIZE, "total": (page_no - 1) * PAGE_SIZE + len(vods)}

        return {"list": [], "page": page_no, "pagecount": 1, "limit": PAGE_SIZE, "total": 0}

    # ---------------- 搜索 ----------------

    def searchContent(self, key, quick=False, pg="1"):
        kw = _text(key)
        if not kw:
            return {"list": [self._note_vod("请输入关键词", "在壳的搜索框里打剧名再搜。")]}
        try:
            d = self._get("/api/search", {"keyword": kw}, timeout=40)
        except Exception as e:
            return {"list": [self._note_vod("搜索没成功", self._err_text(e))]}
        vods = [self._vod(it) for it in (d.get("list") or [])]
        if not vods:
            msg = "没搜到「%s」。\n换个更短的关键词，或者用拼音缩写再试。" % kw
            fails = d.get("failed") or []
            if fails:
                msg += "\n\n有站源这次没答上来：\n" + "\n".join(
                    "· %s：%s" % (_text(f.get("name")), _text(f.get("error"))) for f in fails[:5])
            return {"list": [self._note_vod("没搜到", msg)]}
        return {"list": vods[:120]}

    # ---------------- 详情 ----------------

    def detailContent(self, array):
        vids = array if isinstance(array, (list, tuple)) else [array]
        out = []
        for vid in vids[:10]:
            payload = _b64d(vid) if isinstance(vid, str) else None
            if not payload:
                continue
            kind = payload.get("t")
            if kind == "none":
                name = payload.get("n") or "说明"
                msg = payload.get("msg") or "这次没拉到内容，回头再点一次。"
                out.append(self._note_vod(name, msg))
                continue
            if kind == "diag":
                out.append(self._diag_vod())
                continue
            if kind != "v":
                continue
            sid, did = payload.get("s") or "", payload.get("i") or ""
            if not sid or not did:
                continue
            try:
                d = self._get("/api/detail", {"source": sid, "id": did}, timeout=30)
            except Exception as e:
                out.append(self._note_vod("详情没取到", self._err_text(e)))
                continue
            item = d.get("item") or {}
            eps = item.get("episodes") or []
            play_urls = []
            for i, ep in enumerate(eps):
                idx = ep.get("idx") or (i + 1)
                name = _text(ep.get("name")) or ("第%d集" % idx)
                code = _b64e({"t": "p", "s": sid, "i": did, "e": idx, "n": _text(item.get("name"))})
                play_urls.append("%s$%s" % (name, code))
            vod = self._vod({
                "id": did, "name": item.get("name"), "pic": item.get("pic"),
                "remarks": item.get("remarks") or (("全%d集" % len(eps)) if eps else ""),
                "typeName": item.get("typeName"), "year": item.get("year"),
                "area": item.get("area"), "source": sid,
            })
            vod["vod_content"] = _text(item.get("desc")) or "暂无简介"
            vod["vod_play_from"] = "真果鉴·" + _text(item.get("sourceName"))
            vod["vod_play_url"] = "#".join(play_urls) if play_urls else ("没有可播地址$" + _b64e({"t": "none", "n": "没有可播地址"}))
            out.append(vod)
        return {"list": out}

    # ---------------- 播放 ----------------

    def playerContent(self, flag, id, vipFlags=None):
        if isinstance(id, str) and (id.startswith("http://") or id.startswith("https://")):
            return {"parse": 0, "playUrl": "", "url": id, "header": {"User-Agent": UA}}
        payload = _b64d(id) if isinstance(id, str) else None
        if not payload:
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}
        if payload.get("t") == "none":
            return {"parse": 0, "playUrl": "", "url": "", "header": {},
                    "msg": payload.get("msg") or "这张卡是说明，没有可播内容。"}
        if payload.get("t") != "p":
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}

        try:
            d = self._get("/api/play", {
                "source": payload.get("s") or "",
                "id": payload.get("i") or "",
                "ep": payload.get("e") or 1,
            }, timeout=35)
        except Exception as e:
            return {"parse": 0, "playUrl": "", "url": "", "header": {},
                    "msg": "取播放地址失败：%s" % self._err_text(e)}

        url = d.get("url") or ""
        if not url:
            return {"parse": 0, "playUrl": "", "url": "", "header": {},
                    "msg": d.get("error") or "这一集暂时没有可播地址，换一集或换个站源试试。"}
        hdr = {"User-Agent": UA}
        for k, v in (d.get("headers") or {}).items():
            if v:
                hdr[k] = v
        hdr.setdefault("Referer", (self.base or SERVER_URL) + "/")
        return {"parse": 0, "playUrl": "", "url": url, "header": hdr}

    # ---------------- 自检 ----------------

    def _diag_lines(self):
        lines = []
        try:
            h = self._get("/api/health", timeout=8)
            lines.append("服务：%s %s" % (_text(h.get("title")) or "真果·鉴 Node", _text(h.get("version"))))
            lines.append("地址：%s" % (self.base or SERVER_URL))
            lines.append("可用站源：%s / %s" % (h.get("readySources"), h.get("totalSources")))
            if h.get("native"):
                lines.append("原生接管：已开启（20 个原站 1:1）")
        except Exception as e:
            lines.append("服务没连上：%s" % self._err_text(e))
            lines.append("")
            lines.append("先跑起服务再回来：node server.js --port 8992")
            return lines
        lines.append("")
        try:
            d = self._get("/api/diag", timeout=60)
            for s in (d.get("sources") or []):
                if s.get("ready"):
                    mark = "✓" if s.get("ok") else "✗"
                    detail = ("%s 个分类，%sms" % (s.get("categories"), s.get("ms"))) if s.get("ok") else _text(s.get("error"))
                    lines.append("%s %s（%s）：%s" % (mark, _text(s.get("name")), _text(s.get("group")), detail))
                else:
                    lines.append("· %s（%s）：%s" % (_text(s.get("name")), _text(s.get("group")), _text(s.get("note")) or "适配器待移植"))
        except Exception as e:
            lines.append("自检明细没取到：%s" % self._err_text(e))
        return lines

    def _diag_vod(self):
        text = "\n".join(self._diag_lines())
        return {
            "vod_id": _b64e({"t": "diag", "n": "🩺 服务自检"}),
            "vod_name": "🩺 服务自检",
            "vod_pic": "",
            "vod_remarks": "明细",
            "vod_tag": "",
            "vod_douban_id": 0,
            "vod_content": text,
            "vod_play_from": "真果鉴",
            "vod_play_url": "说明$" + _b64e({"t": "none"}),
        }

    # ---------------- 本地代理兜底 ----------------

    def localProxy(self, param):
        try:
            target = ""
            if isinstance(param, dict):
                target = param.get("url") or param.get("u") or ""
            elif isinstance(param, str):
                target = param
            if not target:
                return [404, "text/plain", "no url"]
            return [302, "text/plain", "", {"Location": target}]
        except Exception as e:
            return [500, "text/plain", str(e)]
