# Neon Drift

<img width="2559" height="1599" alt="Screenshot 2026-02-22 124654" src="https://github.com/user-attachments/assets/9f622d07-e04f-43c6-abea-2445f15c55c0" />

A browser-based arcade game built with HTML5 Canvas. Navigate a glowing orbiter through a cyberpunk corridor by swinging around neon anchors and releasing at the right moment to drift forward.

## How to Play

**Hold** Space / click / tap to latch onto an anchor and orbit it.
**Release** to detach and drift forward.

Chain same-colored anchors to build a combo multiplier. Survive as long as possible — the world accelerates over time.

| Anchor | Effect |
|--------|--------|
| 🟦 Blue (medium) | Standard bonus |
| 🟩 Green (small) | High-risk, high-reward (×10) |
| 🟥 Red (large) | Score drain — avoid long orbits |

## Controls

| Input | Action |
|-------|--------|
| `Space` (hold) | Orbit |
| `Space` (release) | Drift |
| Mouse left button | Hold to orbit, release to drift |
| Touch | Hold to orbit, release to drift |
| `Escape` | Return to boot screen |

## Running Locally

No build step required — open `index.html` directly in a browser.

```
git clone <repo-url>
cd neon-drift
open index.html
```

> A local server (e.g. `npx serve .`) may be needed if your browser blocks
autoplay video or audio from `file://`.

## Stack

- Vanilla JavaScript (single file, ~1300 lines)
- HTML5 Canvas API
- No dependencies or frameworks
