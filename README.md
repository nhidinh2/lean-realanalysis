# lean-realanalysis

A personal **practice project** for getting comfortable with **Lean 4** and [Mathlib](https://github.com/leanprover-community/mathlib4). I work through classic introductory **real analysis** exercises (sums, sets, ℝ, limits, continuity, etc.) and formalize the proofs in Lean instead of only doing them on paper.

It doubles as a sandbox for tactics, type class search, and Mathlib’s analysis API—things that are easy to read about but only stick after you actually prove theorems.

## Overleaf

Parallel **LaTeX** notes (informal write-ups of the same material) live on Overleaf:

**[Open in Overleaf](https://www.overleaf.com/read/czsfymttzjfg#1095ee)**

## What’s in here

Most of the work is in **`math444_hw.lean`**: a long single file with many small problems, each in its own `section`, with comments pointing at textbook-style section numbers (§1.2, §2.1, …) so I can match them to the book while I practice.

The **`LeanRealanalysis`** package is the Lake scaffold (`LeanRealanalysis/` + `LeanRealanalysis.lean`); the interesting content is the analysis proofs, not the stub module.

## Requirements

- [Elan](https://github.com/leanprover/elan) — Lean is pinned in `lean-toolchain` (**v4.28.0**).
- [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) for VS Code or Cursor.

## Setup

```bash
git clone https://github.com/nhidinh2/lean-realanalysis.git
cd lean-realanalysis
lake update
lake build
```

The first full build can take a while while Mathlib compiles.

## Hacking on it

Open the folder in the editor, edit `math444_hw.lean`, and use the **Infoview** for goals and errors. If the language server acts up after `lake update`, restart it from the Lean extension’s command palette.

`.lake/` holds dependencies and build output and is gitignored.
