# Reversible PT Nets in Lean Prover

`Lean version`: [v4.22.0](https://github.com/leanprover/lean4/tree/v4.22.0).

A proof mechanisation of reversible PT nets.

## Install and usage

This repository use the [Mathlib4](https://github.com/leanprover-community/mathlib4) library. So, you need to [install](https://leanprover-community.github.io/get_started.html) **elan**, **lake** and **lean** (and if you want vscode, [emacs](https://github.com/leanprover-community/lean4-mode) or [neovim](https://github.com/Julian/lean.nvim/)). 

Add following to `likefile.toml`: 
```toml
[[require]]
name = "petri_net"
git = "https://github.com/DanielDavalos93/reversible-pt"
rev = "main"
```
or `require petri_net from git "https://github.com/DanielDavalos93/reversible-pt"` if you're using `likefile.lean`. Then run:
```
lake exe cache get
lake build
```
