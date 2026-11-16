# lean-realanalysis

A personal **practice project** for getting comfortable with **Lean 4** and [Mathlib](https://github.com/leanprover-community/mathlib4). I work through classic introductory **real analysis** exercises (sums, sets, ℝ, limits, continuity, etc.) and formalize the proofs in Lean instead of only doing them on paper.

It doubles as a sandbox for tactics, type class search, and Mathlib’s analysis API—things that are easy to read about but only stick after you actually prove theorems.

## Overleaf

Parallel **LaTeX** notes (informal write-ups of the same material) live on Overleaf:

**[Open in Overleaf](https://www.overleaf.com/read/czsfymttzjfg#1095ee)**

## What’s in here

```
LeanRealanalysis/
├── RealAnalysis/
│   ├── Math444.lean        MATH 444 real-analysis homework (one section per problem)
│   └── README.md           status + why some problems are still `sorry`
└── ComplexAnalysis/
    ├── HW1.lean … HW6.lean complex-analysis Homeworks 1–6 (Ahlfors)
    └── README.md           status + why some problems are still `sorry`
LeanRealanalysis.lean       imports everything, so `lake build` checks it all
```

Each problem is its own `section`, with comments giving the textbook reference. The README in
each folder lists which problems are still `sorry` and why.

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

Open the folder in the editor, edit the files under `LeanRealanalysis/`, and use the **Infoview** for goals and errors. If the language server acts up after `lake update`, restart it from the Lean extension’s command palette.

`.lake/` holds dependencies and build output and is gitignored.
