import Poe.Lint

/-!
# D0 negative example

`double`/`absInt`/`sumList` show the linter accepting the fragment; this
file shows it actually rejecting something, so "accepts" isn't just
"never tried to reject". `Vec` is a genuinely value-indexed type (`n` is
a free `Nat` index, not a proof) — the kind of dependent typing increment
1 is meant to keep out of computational positions. (`Fin n` alone doesn't
demonstrate this: it's a single-field structure whose proof field erases
away, collapsing to plain `Nat` at mono LCNF.)
-/

namespace Poe.Examples

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

def vheadOfFragment {α} {n} (v : Vec α (n + 1)) : α :=
  match v with
  | .cons a _ => a

#eval Poe.Lint.check ``vheadOfFragment

end Poe.Examples
