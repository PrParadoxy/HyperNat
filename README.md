# Hypernatural Numbers in Lean 4

This repository contains a minimal Lean 4 formalization of hypernatural numbers constructed from scratch. The development is deliberately compact, self-contained, and avoids Mathlib4 dependencies as much as possible. Apart from `List` and `Set` from Mathlib4, all concepts are implemented directly.

The entire project is approximately 300 lines of code and consists of five files. It was developed by me and [Prof. David Gross](https://www.thp.uni-koeln.de/gross/) (University of Cologne).

## Overview

The goal of the project is to formalize the construction of hypernatural numbers as a quotient of sequences of natural numbers modulo an ideal. The development includes:

- Ideal.lean: Defines of ideals over subsets of ℕ and their properties.
- Lang.lean: Defines formal language of arithmetic with syntax and semantics.
- Def.lean: Constructs the hypernaturals as equivalence classes of sequences.
- Los.lean: Contains formal proof of Łoś's theorem.
- Example.lean: Uses the developed API to prove that every hypernatural is either even or odd.
