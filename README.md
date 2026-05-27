# AJ Gravity Simulator

An interactive N-body gravity simulation with orbiting planets, stellar evolution, and real-time controls.

**Live site:** https://ajgravitysimulator.ajt3317.workers.dev/

## What's in here

- `index.html` — the page (UI, panel, equation bar)
- `gravity.js` — the simulation engine and rendering

No build step, no dependencies. Pure HTML + JS, plus the MathJax and Google Fonts CDNs loaded from `index.html`.

## Running locally

Open `index.html` directly in a browser, or serve the folder:

```bash
python -m http.server 8000
# then visit http://localhost:8000/
```

## Deploying to Cloudflare Pages

1. Push this repo to GitHub.
2. Cloudflare dashboard → **Workers & Pages → Create → Pages → Connect to Git**.
3. Pick this repo.
4. Build settings: **Framework preset:** None · **Build command:** _(empty)_ · **Build output directory:** `/`.
5. Deploy. Pushes to the default branch auto-redeploy.
