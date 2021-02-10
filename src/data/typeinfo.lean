/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

/-!
# Tools for inspecting type information

This module provides `typeinfo T`, which can be used to inspect information about the type `T`.

These are particularly useful for defining notation that unpacks existing notation, for instance:
```
notation A ` →ₗₘ[`:25 R:25 `] ` N := multilinear_map R (typeinfo.pi_codomain (typeinfo.of A)) N
```
which allows `(Π i, M i) →ₗₘ[R] N` and computes `typeinfo.pi_codomain (typeinfo.of A) = λ i, M i`.

When using these projections for notation, it is important to _not_ use dot notation, as otherwise
the pretty printer will not use the notation.
-/

/-- A value which wraps a type. -/
inductive typeinfo (α : Type*)
| of [] : typeinfo

/-- Get the type of the domain of a function type. -/
abbreviation typeinfo.domain {α : Type*} {β : α → Type*}
  (a : typeinfo (Π (i : α), β i)) : Type* := α

/-- Get the type of the codomain of a function type. -/
abbreviation typeinfo.codomain {α β :Type*}
  (a : typeinfo (α → β)) : Type* := β

/-- Get the type of the codomain of a dependent function type. -/
abbreviation typeinfo.pi_codomain {α : Type*} {β : α → Type*}
  (a : typeinfo (Π (i : α), β i)) : α → Type* := β
