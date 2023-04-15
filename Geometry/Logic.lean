/-
https://github.com/leanprover/lean/blob/72a965986fa5aeae54062e98efb3140b2c4e79fd/library/init/logic.lean#L539-L544
https://github.com/leanprover-community/mathlib4/blob/5230db6df2ef97710db9e1c217513ec17566814c/Mathlib/Init/Logic.lean#L212-L217
-/
def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean TSyntax.Compat in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()


def AtMostOne (p : α → Prop) := ¬∃ x y : α, x ≠ y ∧ p x ∧ p y

open Lean TSyntax.Compat in
macro "∃? " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``AtMostOne xs b

@[app_unexpander AtMostOne] def unexpandAtMostOne : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃? $xs:binderIdent*, $b) => `(∃? $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                      => `(∃? $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)               => `(∃? ($x:ident : $t), $b)
  | _                                               => throw ()

theorem all_then_not_exists_not {p : α → Prop} (h : ∀ x : α, p x) : ¬∃ x : α, ¬p x :=
  fun ⟨x, hnp⟩ => hnp (h x)
example {p : α → Prop} (h : ¬∀ x : α, p x) : ∃ x : α, ¬p x := sorry
theorem not_exists_not {p : α → β → Prop} : 
  (∀ a : α, ∀ b : β, p a b) → ¬∃ a : α, ∃ b : β, ¬p a b
:=
  fun h ⟨a, b, hnp⟩ => hnp (h a b)
