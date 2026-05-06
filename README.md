# Reversible PT Nets in Lean Prover

`Lean version`: [v4.29.1](https://github.com/leanprover/lean4/tree/v4.29.1).

This repository contains a full formalization of reversible ocurrence nets in Lean Prover. The organizational structure of the library's files is given by the next graph:

<img width="1507" height="515" alt="library_distribution" src="https://github.com/user-attachments/assets/a3e5f095-07c1-4290-9957-e6143021502d" />

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
