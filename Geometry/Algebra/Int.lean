abbrev ℕ := Nat
#check Int

/-
Integers
-/

inductive ℤ | ofNat (n : ℕ) | negSucc (n : ℕ)
namespace ℤ

instance : Coe ℕ ℤ where coe := ofNat
instance : OfNat ℤ n where ofNat := n
instance : Inhabited ℤ where default := (default : ℕ)

def abs : ℤ → ℕ | ofNat n => n | negSucc n => n.succ
postfix:max "⁺" => Nat.succ
instance : Neg ℤ where neg
  | 0 => 0
  | n⁺ => negSucc n
  | negSucc n => n⁺
#check (-(1 + 2) : Int)
example : negSucc 0 = -1 := rfl

private def subN (M n : ℕ) : ℤ :=
  match (n - M : ℕ) with
  | 0 => M - n
  | .succ k => negSucc k
instance : Add ℤ where add
  | ofNat M, ofNat n => M + n
  | ofNat M, negSucc n => subN M n.succ
  | negSucc M, ofNat n => subN n M.succ
  | negSucc M, negSucc n => negSucc (M + n).succ
instance : Sub ℤ where sub := (. + -.)
instance : Mul ℤ where mul
  | ofNat M, ofNat n => M * n
  | ofNat M, negSucc n => -(M * n.succ : ℕ)
  | negSucc M, ofNat n => -(M.succ * n : ℕ)
  | negSucc M, negSucc n => M.succ * n.succ

-- instance : HPow ℤ ℕ ℤ where hPow := let rec pow := fun | _, 0 => 1 | M, .succ n => M * pow M n ; pow
instance : HPow ℤ ℕ ℤ where hPow := pow where pow M
  | 0 => 1
  | .succ n => M * pow M n

private inductive NonNeg : ℤ → Prop | mk (n : ℕ) : NonNeg n
instance : LE ℤ where le (x y) := NonNeg (y - x)
instance : LT ℤ where lt (x y) := x + 1 ≤ y

instance : DecidableEq ℤ
  | ofNat   M, ofNat   n =>
    match decEq M n with
    | isTrue  h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (ℤ.noConfusion . (absurd . h))
  | negSucc M, negSucc n =>
    match decEq M n with
    | isTrue  h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (ℤ.noConfusion . (absurd . h))
  | ofNat   _, negSucc _ => isFalse ℤ.noConfusion
  | negSucc _, ofNat   _ => isFalse ℤ.noConfusion

end ℤ



/-
Rationals
-/

theorem integral_domain {M n : ℕ} : M ≠ 0 → n ≠ 0 → M * n ≠ 0 := by
  intro _ _
  match M, n with
  | .succ M, .succ n => rw [Nat.mul_succ, Nat.add_succ] ; exact Nat.succ_ne_zero _
  -- automatically closed by decide/contradiction?

structure ℚ where (num : ℤ) (den : ℕ) (inv : den ≠ 0)
namespace ℚ

instance : Neg ℚ where neg x := { x with num := -x.num }
instance : Add ℚ where add x y := {
  num := x.num * y.den + x.den * y.num
  den := x.den * y.den
  inv := integral_domain x.inv y.inv
}
instance : Sub ℚ where sub := (. + -.)
instance : Mul ℚ where mul x y := {
  num := x.num * y.num
  den := x.den * y.den
  inv := integral_domain x.inv y.inv
}

end ℚ



section GroupLike

-- structure Magma (α : Type u) where (op : α → α → α)
#check Equivalence
#check DecidableEq

variable (α : Type u)
#check α → α
#check α → α → α

class Inv where
  inv : α → α
@[inherit_doc] postfix:77 "⁻¹" => Inv.inv

class Magma where
  op : α → α → α
local instance [M : Magma α] : CoeFun α (fun _ => α → α) where
  coe := M.op
-- local instance [M : Magma α] : Mul α where
--   mul := M.op
class Semigroup extends Magma α where
  assoc {a b c : α} : (a b) c = a (b c)
class Monoid extends Semigroup α where
  e : α
  identity {a : α} : e a = a ∧ a e = a
-- local instance [M : Monoid α] : OfNat α (nat_lit 1) where
--   ofNat := M.id
class Group extends Monoid α where
  inv : α → α
  inverse {a : α} : inv a a = e ∧ a (inv a) = e
-- local instance [M : Group α] : Inv α where
--   inv := M.inv
class AbGrp extends Group α where
  comm {a b : α} : a b = b a

#print Group
#print AbGrp
end GroupLike

section RingLike

-- example [A : AbGrp α] : A.ofNat = 1 := rfl

-- instance : AbGrp ℤ where
--   op := Add.add
--   assoc := ℤ.add_assoc
--   id := 0
--   identity {a} := ⟨ℤ.zero_add a, ℤ.add_zero a⟩
--   inv := Neg.neg
#check Nat.zero_add

class AddSemigroup (α : Type u) extends Add α where
  add_assoc {a b c : α} : (a + b) + c = a + (b + c)

class HasZero (α : Type u) where
  zero : α
instance [A : HasZero α] : OfNat α (nat_lit 0) where
  ofNat := A.zero

section
variable {a : Type u} [AddSemigroup α] [HasZero α]

instance : HMul Nat α α where
  hMul := hMul
where hMul (n : Nat) (a : α) :=
  match n with
  | 0 => 0
  | .succ n => hMul n a + a

theorem AddMonoid.zero_mul {a : α} : 0 * a = 0 := rfl
end

class AddMonoid (α : Type u) extends AddSemigroup α, HasZero α where
  zero_add {a : α} : 0 + a = a
  add_zero {a : α} : a + 0 = a

section
variable {a : Type u} [AddMonoid α]

theorem AddMonoid.one_mul {a : α} : 1 * a = a := calc
  1 * a = 0 * a + a := rfl
      _ =     0 + a := by rw [zero_mul]
      _ =         a := zero_add

variable [Neg α]

instance : HMul Int α α where
  hMul := hMul
where hMul (n : Int) (a : α) : α :=
  match n with
  | .ofNat n => n * a
  | .negSucc n => -(n.succ * a)

theorem AddGroup.neg_one_mul {a : α} : -1 * a = -a := calc
  -1 * a = -(1 * a) := rfl
       _ = -a       := by rw [AddMonoid.one_mul]
end

instance [Add α] [Neg α] : Sub α where
  sub (a b) := a + (-b)

class AddGroup (α : Type u) extends AddMonoid α, Neg α where
  neg_add {a : α} : -a + a = 0
  add_neg {a : α} : a - a = 0

class AddAbGrp (α : Type u) extends AddGroup α where
  add_comm {a b : α} : a + b = b + a

example [A : AddGroup α] : A.zero = 0 := rfl

class MulSemigroup (α : Type u) extends Mul α where
  mul_assoc {a b c : α} : (a * b) * c = a * (b * c)
class HasOne (α : Type u) where
  one : α
instance [A : HasOne α] : OfNat α (nat_lit 1) where
  ofNat := A.one
instance [MulSemigroup α] [HasOne α] : HPow α Nat α where
  hPow := hPow
where hPow (a : α) (n : Nat) : α := match n with
  | 0 => 1
  | .succ n => hPow a n * a
class MulMonoid (α : Type u) extends MulSemigroup α, HasOne α where
  one_mul {a : α} : 1 * a = a
  mul_one {a : α} : a * 1 = a
instance [MulMonoid α] [Inv α] : HPow α Int α where
  hPow := hPow
where hPow (a : α) (n : Int) : α := match n with
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ n.succ)⁻¹
instance [Mul α] [Inv α] : Div α where
  div (a b) := a * b⁻¹
class MulGroup (α : Type u) extends MulMonoid α, Inv α where
  inv_mul {a : α} : a⁻¹ * a = 1
  mul_inv {a : α} : a / a = 1
class MulAbGrp (α : Type u) extends MulGroup α where
  mul_comm {a b : α} : a * b = b * a

-- inductive Rng : Type u → Type u where
--   | mk {α : Type u} [Monoid α] (inv : α → α) (_ : ∀ {a : α}, inv a * a = 1 ∧ a * inv a = 1) : Rng α

class Rng (α : Type u) extends AddAbGrp α, MulSemigroup α where
  left_distrib {a b c : α} : a * (b + c) = a * b + a * c
  right_distrib {a b c : α} : (a + b) * c = a * c + b * c
class Ring (α : Type u) extends Rng α, MulMonoid α
instance [R : Ring α] : Coe Int α where
  coe n := n * R.one
instance [Ring α] : OfNat α n where
  ofNat := n
-- def Ring.char [R : Ring α] : Nat :=
--   let characteristic (n : Nat) := n > 0 ∧ n = R.zero
--   if ∃ n : Nat, characteristic n then 1 else 0
class CommRing (α : Type u) extends Ring α where
  mul_comm {a b : α} : a * b = b * a
class IntegralDomain (α : Type u) extends CommRing α where
  zero_divisor {a b : α} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 -- a * b = 0 → a = 0 ∨ b = 0
class UFD (α : Type u) extends IntegralDomain α  -- TODO
class EuclideanDomain (α : Type u) extends IntegralDomain α where
  norm : α → Nat
  div_thm (a b : α) : ∃ q r : α, (a = b * q + r) ∧ (norm r < norm b)
instance [R : EuclideanDomain α] : Coe α (UFD α) where
  coe := sorry

#check Subtype
#check {x : Nat // x ≠ 1}
#check subtypeCoe
structure Nonzero (α : Type u) [HasZero α] where
  val : α
  nonzero : val ≠ (0 : α)
postfix:max "ˣ" => Nonzero
instance [HasZero α] : CoeHead αˣ α where
  coe a := a.val

instance [HasZero α] [Mul α] [Inv αˣ] : HDiv α αˣ α where
  hDiv (a b) := a * b⁻¹

class Field (α : Type u) extends CommRing α, Inv αˣ where
  inv_mul {a : αˣ} : a⁻¹ * (a:α) = 1
  mul_inv {a : αˣ} : (a:α) / a = 1
instance [F : Field α] : IntegralDomain α where
  zero_divisor := sorry
-- instance [F : Field α] : MulAbGrp αˣ where
--   mul (a b) := {
--     val := F.mul a b
--     nonzero := IntegralDomain.zero_divisor a.nonzero b.nonzero
--   }
--   one := { val := 1, nonzero := sorry}

end RingLike

section ModuleLike

class Vect (F : Type u) (V : Type v) [Field F] extends AddAbGrp V, HMul F V V where
  one_mul {x : V} : (1:F) * x = x
  mul_assoc {a b : F} {x : V} : (a * b) * x = a * (b * x)
  left_distrib {a : F} {x y : V} : a * (x + y) = a * x + a * y
  right_distrib {a b : F} {x : V} : (a + b) * x = a * x + b * x

end ModuleLike