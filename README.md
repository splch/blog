# Blog

A static blog with no build step. The browser finds the Markdown files in `content/`, renders them with [marked](https://github.com/markedjs/marked), and routes by hash (`#/id`).

To publish, add the next numbered file (`content/56.md`). The site probes ids 1, 2, 4, 8, … until one is missing and loads every id below it, so keep ids contiguous.

Front matter:

```yaml
title: Post title
date: 2026-04-12 # omit for pages without a dated header
image: a.webp, b.webp # files in images/ or full URLs
video: clip.mp4 # files in data/ or embed URLs
audio: music/song.mp3 # files in data/
canvas: true # generated art banner
post: false # nav page instead of a post
archive: true # reachable by URL, hidden from the list
```

Libraries (marked, highlight.js, KaTeX) load in the background, so the post list renders without waiting on them.
