import Halmos.Nat
set_option linter.unusedVariables false
set_option autoImplicit false

inductive ℤ | pos: ℕ → ℤ | negSucc: ℕ → ℤ
namespace ℤ

postfix:arg "↓" => pos
postfix:arg "⁻" => negSucc
instance: Coe ℕ ℤ where coe := pos
instance: OfNat ℤ (nat_lit 0) where ofNat := 0↓
instance: OfNat ℤ (nat_lit 1) where ofNat := 1↓
#check (0: ℤ)
#check ↑0
#check 0

-- class HAbs (α: outParam (Type _)) (β: Type _) where hAbs: α → β
-- class HAbs (α : Type u) (β : Type v) where hAbs : α → β
-- macro:arg "∣" a:term "∣" : term => `(HAbs.hAbs $a)

instance {α} [Add α] [Neg α]: Sub α where sub a b := a + (-b)

-- instance: HAbs ℤ ℕ where hAbs | n↓ => n | n⁻ => n⁺
-- #check (∣1∣ + 1)↓

instance: HSub ℕ ℕ ℤ where hSub m n :=
  match (n.sub m) with | 0 => m.sub n | k⁺ => k⁻

def add: ℤ → ℤ → ℤ
  | m↓, n↓ => m + n
  | m↓, n⁻ => m - n⁺
  | m⁻, n↓ => n - m⁺
  | m⁻, n⁻ => (m + n)⁺⁻
instance: Add ℤ where add := add

variable {a b c : ℤ} {m n k : ℕ}
def ofPos: m = n → m↓ = n↓ := congrArg pos
-- instance : Coe (m = n) (pos m = pos n) where coe := congrArg pos
theorem add_zero: a + 0 = a :=
  match a with | a⁻ => rfl | a↓ => ofPos ℕ.add_zero
theorem zero_add: 0 + a = a :=
  match a with | a⁻ => rfl | a↓ => ofPos ℕ.zero_add
theorem add_comm: b + a = a + b :=
  match a, b with
  | m↓, n↓ => ofPos ℕ.add_comm
  | m↓, n⁻ => rfl
  | m⁻, n↓ => rfl
  | m⁻, n⁻ => congrArg (.⁺⁻) ℕ.add_comm
theorem add_succ: a + n⁺ = a + n + 1 :=
  match a with
  | a↓ => rfl
  | a⁻ => by rw [ℕ.add_one.symm] ; induction n with
          | zero => rfl
          | succ n ih => sorry
theorem succ_sub: m⁺ - n = (m - n) + 1↓ :=
  sorry
theorem subNatNat_add_pos: m - n + k↓ = (m + k) - n :=
  k.rec add_zero fun a ih => by rw [ℕ.add_succ, succ_sub, add_succ, ih] ; rfl
theorem pos_add_subNatNat: k↓ + (m - n) = (k + m) - n :=
  by rw [add_comm, ℕ.add_comm, subNatNat_add_pos]
theorem subNatNat_add_succ': m - n + k⁻ = m - (n + k⁺) :=
  sorry
theorem succ'_add_subNatNat: k⁻ + (m - n) = m - (k⁺ + n) :=
  by rw [add_comm, ℕ.add_comm, subNatNat_add_succ']
#check Int
theorem add_assoc: a + (b + c) = (a + b) + c :=
  match a, b, c with
  | a↓, b↓, c↓ => ofPos ℕ.add_assoc
  | a↓, b⁻, c↓ => calc a↓ + (c - b⁺)
                     = (a + c) - b⁺     := pos_add_subNatNat
               (_:ℤ) = a - b⁺ + c       := subNatNat_add_pos.symm
  | a⁻, b↓, c↓ => subNatNat_add_pos.symm
  | a⁻, b⁻, c↓ => calc a⁻ + (c - b⁺)
                     = c - (a⁺ + b⁺)    := succ'_add_subNatNat
               (_:ℤ) = c - (a + b⁺)⁺    := by rw [ℕ.succ_add]
  | a↓, b↓, c⁻ => pos_add_subNatNat
  | a↓, b⁻, c⁻ => calc a - (b + c⁺)⁺
                     = a - (b⁺ + c⁺)    := by rw [ℕ.succ_add]
                   _ = a - b⁺ + c⁻      := subNatNat_add_succ'.symm
  | a⁻, b↓, c⁻ => calc a⁻ + (b - c⁺)
                     = b - (a⁺ + c⁺)    := succ'_add_subNatNat
                   _ = b - a⁺ + c⁻      := subNatNat_add_succ'.symm
  | a⁻, b⁻, c⁻ => calc (a + (b + c⁺))⁺⁻
                     = (a⁺ + (b + c⁺))⁻ := by rw [ℕ.succ_add]
                   _ = ((a⁺ + b) + c⁺)⁻ := by rw [ℕ.add_assoc]
                   _ = ((a + b)⁺ + c⁺)⁻ := by rw [ℕ.succ_add]

instance: Neg ℤ where neg | 0 => 0 | n⁺ => n⁻ | n⁻ => n⁺
theorem sub_self: a - a = 0 :=
  sorry

-- theorem zz1: ℕ.zero = (0:ℤ) := rfl
-- theorem add_assocℤℕℕ: a + (m + n) = a + m + n := by
--   induction n with
--   | zero => rw [zz1, add_zero, add_zero]
--   | succ n ih =>
--       match a with
--       | a↓ => exact ofPos ℕ.add_assoc
--       | a⁻ =>
--           calc a + (m↓ + n⁺↓)
--             = a + (m + n⁺)↓ := rfl
--           _ = a + (m + n)⁺↓ := rfl
--           _ = sorry

theorem sub_nat_nat_add {m n k: ℕ}: m↓ + (n - k) = (m + n) - k := by
  induction k with
  | zero => apply ofPos ; rfl
  | succ k ih => sorry
    -- have: m + (n - k⁺) = m + (n + k⁻) := rfl ; rw [this]
theorem add_assoc_aux1 {m n: ℕ}: {c: ℤ} → m↓ + (n↓ + c) = m↓ + n↓ + c
  | c↓ => ofPos ℕ.add_assoc
  | c⁻ => show m↓ + (n - c⁺) = (m + n) - c⁺ from sub_nat_nat_add

end ℤ
