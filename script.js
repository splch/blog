// Posts are content/<id>.md files, discovered and rendered in the browser.
// Libraries load on demand: the post list renders without them, and they
// download in the background (or alongside a linked post) for later use.

const CDN = "https://cdn.jsdelivr.net/npm/";
const STYLES = {
  light: [
    `${CDN}highlight.js@11.11.1/styles/github.min.css`,
    "sha384-eFTL69TLRZTkNfYZOLM+G04821K1qZao/4QLJbet1pP4tcF+fdXq/9CdqAbWRl/L",
    "(prefers-color-scheme: light)",
  ],
  dark: [
    `${CDN}highlight.js@11.11.1/styles/github-dark-dimmed.min.css`,
    "sha384-PiLidnnRuzFgp4qiN8oGNmktrV8ETL+6a8heAxljUX4A+3XWlocwaMn9duBUepfK",
    "(prefers-color-scheme: dark)",
  ],
  katex: [
    `${CDN}katex@0.16.45/dist/katex.min.css`,
    "sha384-UA8juhPf75SzzAMA/4fo3yOU7sBJ0om7SCD2GHq0fZqZco6tr1UCV7nUbk9J90JM",
  ],
};

const esc = (s) => s.replace(/[&<>"']/g, (c) => `&#${c.charCodeAt(0)};`);
// Memoize an async loader, forgetting failures so a later call can retry.
const once = (f) => {
  let p;
  return () =>
    (p ??= f().catch((e) => {
      p = null;
      throw e;
    }));
};
const stylesheet = ([href, integrity, media = "all"]) =>
  new Promise((done) =>
    document.head.append(
      Object.assign(document.createElement("link"), {
        rel: "stylesheet",
        href,
        integrity,
        media,
        crossOrigin: "anonymous",
        onload: done,
        onerror: done,
      }),
    ),
  );

/* ===== Markdown ===== */

let hljs;
const loadMarked = once(async () => {
  const [{ marked }, { markedHighlight }] = await Promise.all([
    import("marked"),
    import("marked-highlight"),
  ]);
  return marked.use(
    markedHighlight({
      highlight: (code, lang) =>
        hljs?.getLanguage(lang)
          ? hljs.highlight(code, { language: lang }).value
          : code,
    }),
    { breaks: true },
  );
});
const loadHighlight = once(() =>
  Promise.all([
    import("highlight.js").then((m) => (hljs = m.default)),
    stylesheet(STYLES.light),
    stylesheet(STYLES.dark),
  ]),
);
const loadKatex = once(() =>
  Promise.all([
    Promise.all([loadMarked(), import("marked-katex-extension")]).then(
      ([marked, { default: markedKatex }]) =>
        marked.use(markedKatex({ throwOnError: false })),
    ),
    stylesheet(STYLES.katex),
  ]),
);

// Fetch every library without blocking anything: a post opened later then
// renders without waiting on the network.
const warm = () =>
  Promise.all([loadMarked(), loadHighlight(), loadKatex()]).catch(() => {});

async function markdown(body) {
  const [marked] = await Promise.all([
    loadMarked(),
    /```|~~~/.test(body) && loadHighlight(),
    body.includes("$") && loadKatex(),
  ]);
  return marked
    .parse(body)
    .replace(
      /<table[\s>][\s\S]*?<\/table>/g,
      (t) =>
        `<div class="table-wrap" tabindex="0" role="region" aria-label="Scrollable table">${t}</div>`,
    )
    .replace(/<pre>/g, '<pre tabindex="0">');
}

/* ===== Content ===== */

function parse(text) {
  const [, front, ...rest] = text.split("---\n");
  const meta = Object.fromEntries(
    [...front.matchAll(/^(.+?):(.*)/gm)].map(([, k, v]) => [
      k.trim(),
      v.trim(),
    ]),
  );
  const body = rest.join("---\n");
  return {
    ...meta,
    post: meta.post !== "false",
    body,
    minutes: Math.ceil(body.split(/\s+/).length / 230),
  };
}

const cache = {};
const load = (id, priority = "low") =>
  (cache[id] ??= fetch(`content/${id}.md`, { priority })
    .then((r) => r.ok && r.text())
    .then((t) => t && { id: `${id}`, ...parse(t) })
    .catch((e) => {
      delete cache[id];
      throw e;
    }));

// Probe ids 1, 2, 4, … until one is missing, then load every id below it.
// Probes up to 128 go out together; larger blogs keep doubling from there.
async function discover() {
  for (let p = 1; p <= 128; p *= 2) load(p);
  let hi = 1;
  while (await load(hi)) hi *= 2;
  const ids = [...Array(hi).keys(), "not-found"];
  return (await Promise.all(ids.map((id) => load(id)))).filter(Boolean);
}

/* ===== Views ===== */

const items = (v) => v.split(/\s*,\s*/).filter(Boolean);
const media = {
  canvas: () => `<canvas id="gen-canvas" width="1200" height="300"></canvas>`,
  audio: (v) =>
    items(v)
      .map((s) => {
        const name = esc(s.replace(/.*\//, "").replace(/\.[^.]+$/, ""));
        return `<label>${name}<audio controls preload="metadata" src="data/${esc(s)}" aria-label="${name}"></audio></label>`;
      })
      .join(""),
  video: (v, title) =>
    `<div class="gallery" tabindex="0" role="region" aria-label="Video gallery">${items(
      v,
    )
      .map((s) =>
        s.includes("://")
          ? `<iframe src="${esc(s)}" title="${title}" loading="lazy" allow="autoplay; encrypted-media; fullscreen"></iframe>`
          : `<video controls preload="metadata" src="data/${esc(s)}" aria-label="${title}"></video>`,
      )
      .join("")}</div>`,
  image: (v, title) =>
    `<div class="gallery" tabindex="0" role="region" aria-label="Image gallery">${items(
      v,
    )
      .map(
        (s, i) =>
          `<img src="${esc(s.includes("://") ? s : `images/${s}`)}" alt="${title}" ${i ? 'loading="lazy"' : 'fetchpriority="high"'}>`,
      )
      .join("")}</div>`,
};

// De Jong attractor, varied per post by golden-ratio offsets of its id.
function drawArt(canvas, id) {
  const g = canvas.getContext("2d"),
    { width: W, height: H } = canvas;
  const [A, B, C, D] = [1.4, -2.3, 2.4, -2.1].map(
    (n, i) => n + (((id * 0.618 * (i + 1)) % 1) - 0.5) * 0.6,
  );
  const cx = W * (0.3 + ((id * 0.618) % 1) * 0.4),
    cy = H * (0.3 + ((id * 1.414) % 1) * 0.4);
  g.fillStyle = `hsla(${((id * 137.5) % 360) | 0},70%,55%,.05)`;
  for (let i = 0, x = 0, y = 0, t; i < 60000; i++) {
    t = Math.sin(A * y) - Math.cos(B * x);
    y = Math.sin(C * x) - Math.cos(D * y);
    g.fillRect(cx + ((x = t) * W) / 7, cy + (y * H) / 7, 1, 1);
  }
}

const dateFmt = new Intl.DateTimeFormat("en", {
  month: "short",
  day: "numeric",
  year: "numeric",
});
const fmtDate = (d) => d && dateFmt.format(new Date(d + "T00:00"));
const excerpt = (body) => {
  const text = (/^[\p{L}\p{N}].*/mu.exec(body)?.[0] ?? "")
    .replace(/<[^>]*>/g, "")
    .replace(/\[([^\]]+)\]\([^)]+\)/g, "$1")
    .replace(/[*_`]/g, "");
  return esc(text.length > 160 ? text.slice(0, 160) + "…" : text);
};

const content = document.getElementById("content");
const announcer = document.getElementById("announcer");
let entries, posts, listHTML;
let view = 0; // bumped on every navigation so stale async renders bail out
let shown = {}; // the post on screen and the view that rendered it

function display(html, title, target) {
  content.innerHTML = html;
  scrollTo(0, 0);
  document.title = `${title} | ${location.hostname}`;
  announcer.textContent = document.title;
  const el = (target && content.querySelector(target)) || content;
  el.setAttribute("tabindex", "-1");
  el.focus({ preventScroll: true });
}

function postNav(e) {
  const i = posts ? posts.indexOf(e) : -1;
  const older = i >= 0 && posts[i + 1],
    newer = i >= 0 && posts[i - 1];
  const links =
    (older
      ? `<a rel="prev" href="#/${older.id}">← ${esc(older.title)}</a>`
      : "") +
    (newer
      ? `<a rel="next" href="#/${newer.id}">${esc(newer.title)} →</a>`
      : "");
  return links && `<nav aria-label="Posts">${links}</nav>`;
}

async function showPost(e, seq) {
  let body;
  try {
    body = await (e.html ??= markdown(e.body));
  } catch {
    delete e.html;
    if (seq === view) content.textContent = "Failed to load. Please refresh.";
    return;
  }
  if (seq !== view) return;
  const title = esc(e.title || "");
  const header = e.date
    ? `<header><h1>${title}</h1><p><time datetime="${esc(e.date)}">${fmtDate(e.date)}</time> · ${e.minutes} min read</p></header>`
    : "";
  const extras = Object.keys(media)
    .filter((k) => e[k])
    .map((k) => media[k](e[k], title))
    .join("");
  display(
    `<article>${header}${extras}${body}${postNav(e)}</article>`,
    e.title || "Posts",
    "h1",
  );
  if (e.canvas) drawArt(content.querySelector("#gen-canvas"), +e.id);
  shown = { e, seq };
}

function showList() {
  listHTML ??=
    `<input id="q" type="search" placeholder="Filter" aria-label="Filter posts">` +
    posts
      .map(
        (p) =>
          `<a href="#/${p.id}"><strong>${esc(p.title)}</strong> ` +
          `<small>${fmtDate(p.date)} · ${p.minutes} min read</small>` +
          `<span>${excerpt(p.body)}</span></a>`,
      )
      .join("");
  display(listHTML, "Posts");
  const links = [...content.querySelectorAll("a")].map((a) => [
    a,
    a.textContent.toLowerCase(),
  ]);
  content.querySelector("#q").oninput = (ev) => {
    const q = ev.target.value.toLowerCase();
    for (const [a, text] of links) a.hidden = !!q && !text.includes(q);
  };
}

function markCurrent() {
  const cur = location.hash.startsWith("#/") ? location.hash : "#/";
  for (const a of document.querySelectorAll("#nav a"))
    if (a.getAttribute("href") === cur) a.setAttribute("aria-current", "page");
    else a.removeAttribute("aria-current");
}

function render(event) {
  const hash = location.hash,
    route = hash.startsWith("#/");
  if (event && hash && !route) return; // an in-page anchor, not a route
  const id = route ? hash.slice(2) : "",
    seq = ++view;
  markCurrent();
  if (!id) {
    if (posts) showList();
    else content.textContent = "Loading…";
  } else if (entries) showPost(entries[id] || entries["not-found"], seq);
  else {
    warm();
    return load(id, "high").then((e) => e && showPost(e, seq));
  }
}

// A linked post renders first, before discovery competes for bandwidth.
// Post links and nav pages follow once discovery is done.
addEventListener("hashchange", render);
await render()?.catch(() => {});
const all = await discover().catch(() => null);
if (all) {
  entries = Object.fromEntries(all.map((e) => [e.id, e]));
  posts = all
    .filter((e) => e.post && e.archive !== "true")
    .sort((a, b) => (b.date || "").localeCompare(a.date || ""));
  document.getElementById("nav").insertAdjacentHTML(
    "beforeend",
    all
      .filter((e) => !e.post)
      .map((p) => `<a href="#/${p.id}">${esc(p.title)}</a>`)
      .join(""),
  );
  markCurrent();
  if (shown.seq === view)
    content
      .querySelector("article")
      .insertAdjacentHTML("beforeend", postNav(shown.e));
  else render();
  (window.requestIdleCallback || setTimeout)(warm);
} else if (shown.seq !== view) {
  content.textContent = "Failed to load. Please refresh.";
}
