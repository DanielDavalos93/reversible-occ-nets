# Reversible PT Nets in Lean Prover

`Lean version`: [v4.29.1](https://github.com/leanprover/lean4/tree/v4.29.1).

This repository contains a full formalization of reversible ocurrence nets in Lean Prover. The organizational structure of the library's files is given by the next graph:

<img width="1507" height="515" alt="library_distribution" src="https://github.com/user-attachments/assets/a3e5f095-07c1-4290-9957-e6143021502d" />

### Standard variables for types

* `N : Net α β`
* `M : MarkedNet α β`
* `O : is_occurrence N` if `N : Net α β`
* `MO : is_marked_occurrence M` if `M : MarkedNet α β`
* `R : Reversible α β`
* `RO : ReversibleOccurrence α β`
* `MO : MarkedReversibleOccurrence α β`

### Dependency graph

Futhermore, some of the main definitions, lemmas and theorems dependents to each other over these files are given by:

![dependency_graph](https://raw.githubusercontent.com/DanielDavalos93/reversible-occ-nets/9ce337a8a0bd97d50884cec9bf05a1282e279a01/dependencies_graph.svg)

Definitions are in white, lemmas in orange, and theorems in green.

## Install and usage

This repository use the [Mathlib4](https://github.com/leanprover-community/mathlib4) library. So, you need to [install](https://leanprover-community.github.io/get_started.html) **elan**, **lake** and **lean** (and whichever you prefer: [vscode](https://github.com/leanprover/vscode-lean4), [emacs](https://github.com/leanprover-community/lean4-mode) or [neovim](https://github.com/Julian/lean.nvim/)). 

Add following to `likefile.toml`: 
```toml
[[require]]
name = "petri_net"
git = "https://github.com/DanielDavalos93/reversible-occ-nets"
rev = "main"
```
or `require petri_net from git "https://github.com/DanielDavalos93/reversible-occ-nets"` if you're using `likefile.lean`. Then run:
```
lake exe cache get
lake build
```
