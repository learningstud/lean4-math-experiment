import Algebra.Nat
set_option linter.unusedVariables false

inductive ℤ | pos : ℕ → ℤ | succ' : ℕ → ℤ
namespace ℤ

postfix:arg "↓" => pos
postfix:arg "⁻" => succ'
instance : Coe ℕ ℤ where coe := pos
instance : OfNat ℤ 0 where ofNat := (0:ℕ)
instance : OfNat ℤ 1 where ofNat := (1:ℕ)
#check (0 : ℤ)
#check ↑0

instance : HAbs ℤ ℕ where hAbs | (n:ℕ) => n | n⁻ => n⁺
#check (∣↑1∣ + 1)

instance : HSub ℕ ℕ ℤ where hSub m n :=
  match (n.sub m) with | 0 => m.sub n | k⁺ => k⁻

instance : Add ℤ where add
  | m↓, n↓ => m + n
  | m↓, n⁻ => m - n⁺
  | m⁻, n↓ => n - m⁺
  | m⁻, n⁻ => (m + n)⁺⁻

variable {a b c : ℤ} {m n k : ℕ}
def ofPos : m = n → pos m = pos n := congrArg pos
-- instance : Coe (m = n) (pos m = pos n) where coe := congrArg pos
theorem add_zero : a + 0 = a :=
  match a with | a⁻ => rfl | (a:ℕ) => ofPos ℕ.add_zero
theorem zero_add : 0 + a = a :=
  match a with | a⁻ => rfl | (a:ℕ) => ofPos ℕ.zero_add
theorem add_comm : b + a = a + b :=
  match a, b with
  | m↓, n↓ => ofPos ℕ.add_comm
  | m↓, n⁻ => rfl
  | m⁻, n↓ => rfl
  | m⁻, n⁻ => congrArg (.⁺⁻) ℕ.add_comm
theorem add_succ : a + n⁺ = a + n + 1 :=
  sorry
  -- match a with | a↓ => rfl | a⁻ => succ_sub
theorem succ_sub : m⁺ - n = (m - n) + 1↓ :=
  sorry
theorem subNatNat_add_pos : m - n + k↓ = (m + k) - n :=
  k.rec add_zero fun a ih => by rw [ℕ.add_succ, succ_sub, add_succ, ih] ; rfl
theorem pos_add_subNatNat : k↓ + (m - n) = (k + m) - n :=
  by rw [add_comm, ℕ.add_comm, subNatNat_add_pos]
theorem subNatNat_add_succ' : m - n + k⁻ = m - (n + k⁺) :=
  sorry
theorem succ'_add_subNatNat : k⁻ + (m - n) = m - (k⁺ + n) :=
  by rw [add_comm, ℕ.add_comm, subNatNat_add_succ']
theorem add_assoc : a + (b + c) = (a + b) + c :=
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

instance : Neg ℤ where neg | 0 => 0 | n⁺ => n⁻ | n⁻ => n⁺
theorem sub_self : a - a = 0 :=
  sorry

end ℤ
