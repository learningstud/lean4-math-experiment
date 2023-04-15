#eval (0 : Int) / 0

/-
Mag: magma
UMag: unital magma
Grp: group
Ab: Ableian group
Ring: ring
CRing: commutative ring
Field: field
K-Vect: vector space over K
-/

class AddRightQuasigroup (α : Type u) extends Add α, Neg α where
  sub (a b : α) := a + -b
instance [AddRightQuasigroup α] : Sub α where
  sub a b := AddRightQuasigroup.sub a b

class Zero (α : Type u) where
  zero : α
instance [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

class Ab (α : Type u) extends AddRightQuasigroup α, Zero α where
  add_assoc (a b c : α) : (a + b) + c = a + (b + c)
  add_comm (a b : α) : a + b = b + a
  add_zero (a : α) : a + 0 = a
  add_right_neg (a : α) : a + -a = 0



class Inv (α : Type u) where
  inv : α → α
postfix:100 "⁻¹" => Inv.inv

class MulRightQuasigroup (α : Type u) extends Mul α, Inv α where
  div (a b : α) := a * b⁻¹
instance [MulRightQuasigroup α] : Div α where
  div a b := MulRightQuasigroup.div a b

class One (α : Type u) where
  one : α
instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

class Field (α : Type u) extends Ab α, MulRightQuasigroup α, One α where
  mul_assoc (a b c : α) : (a * b) * c = a * (b * c)
  mul_comm (a b : α) : a * b = b * a
  zero_ne_one : (0 : α) ≠ 1
  mul_one (a : α) : a * 1 = a
  mul_inv_cancel {a : α} : a ≠ 0 → a * a⁻¹ = 1
  right_distrib (a b c : α) : (a + b) * c = (a * c) + (b * c)

/-
# Fields

In what follows we shall have occasion to use various classes of numbers (such as the class of all real numbers or the class of all complex numbers).
Because we should not, at this early stage, commit ourselves to any specific class, we shall adopt the dodge of referring to numbers as scalars.
The reader will not lose anything essential if he consistently interprets scalars as real numbers or as complex numbers; in the examples that we shall study both classes will occur.
To be specific (and also in order to operate at the proper level of generality) we proceed to list all the general facts about scalars that we shall need to assume.
-/

section
variable {K} [Field K] (α β γ : K)
-- (A) To every pair, $α$ and $β$, of scalars there corresponds a scalar $α + β$, called the *sum* of $α$ and $β$, in such a way that
-- (1) addition is commutative, $α + β = β + α$,
example : α + β = β + α := Ab.add_comm α β
-- (2) addition is associative, $α + (β + γ) = (α + β) + γ$,
example : α + (β + γ) = (α + β) + γ := (Ab.add_assoc α β γ).symm
-- (3) there exists a unique scalar $0$ (called zero) such that $α + 0 = α$ for every scalar $α$, and
example : α + 0 = α := Ab.add_zero α
-- (4) to every scalar $α$ there corresponds a unique scalar $-α$ such that $α + (-α) = O$.
example : α + (-α) = 0 := Ab.add_right_neg α
-- (B) To every pair, $α$ and $β$, of scalars there corresponds a scalar $αβ$, called the product of $α$ and $β$, in such a way that
-- (1) multiplication is commutative, $αβ = βα$,
example : α * β = β * α := Field.mul_comm α β
-- (2) multiplication is associative, $α(βγ) = (αβ)γ$,
example : α * (β * γ) = (α * β) * γ := (Field.mul_assoc α β γ).symm
-- (3) there exists a unique non-zero scalar $1$ (called one) such that $α1 = α$ for every scalar $α$, and
example : α * 1 = α := Field.mul_one α
-- (4) to every non-zero scalar a there corresponds a unique scalar $α⁻¹$ (or $1/a$) such that $αα⁻¹ = 1$.
example (h : α ≠ 0) : α * α⁻¹ = 1 := Field.mul_inv_cancel h
-- (C) Multiplication is distributive with respect to addition, $α(β + γ) = αβ + αγ$.
theorem Field.left_distrib : α * (β + γ) = α * β + α * γ := by
  rw [mul_comm, right_distrib, mul_comm, mul_comm γ]
end

/-
If addition and multiplication are defined within some set of objects (scalars) so that the conditions (A), (B), and (C) are satisfied, then that set (together with the given operations) is called a *field*.
Thus, for example, the set $ℚ$ of all rational numbers (with the ordinary definitions of sum and product) is a field, and the same is true of the set $ℝ$ of all real numbers and the set $ℂ$ of all complex numbers.

## Excercises
-/

/-
1. Almost all the laws of elementary arithmetic are consequences of the axioms defining a field.
  Prove, in particular, that if $𝔽$ is a field, and if $α$, $β$, and $γ$ belong to $𝔽$, then the following relations hold.
-/
section
variable {K} [Field K] (α β γ : K)
-- (a) $0 + α = α$.
theorem Ab.zero_add : 0 + α = α := by
  rw [add_comm, add_zero]
-- (b) If $α + β = α + γ$, then $β = γ$.
theorem Ab.add_cancel_left : α + β = α + γ → β = γ := by
  intro h ; rw [add_comm, add_comm α] at h
  have g : β + α + -α = γ + α + -α := congrArg (fun x => x + -α) h
  rw [add_assoc, add_assoc, add_right_neg, add_zero, add_zero] at g
  exact g
-- (c) $α + (β - α) = β$. (Here $β - α = β + (-α)$.)
theorem Ab.add_222 : α + (β - α) = β := by -- type (2,2,2) algebra as a quasigroup
  have h : β - α = β + -α := sorry
  rw [h, add_comm, add_assoc, add_comm (-α), add_right_neg, add_zero]

-- (d) $α·0 = 0·α = 0$. (For clarity or emphasis we sometimes use the dot to indicate multiplication.)
theorem Field.mul_zero : α * 0 = 0 ∧ 0 * α = 0 := by
  apply And.intro
  . have h : α * 0 + 0 = α * 0 + α * 0 := calc
      α * 0 + 0 = α * 0 := Ab.add_zero _
      _ = α * (0 + 0) := by rw [Ab.add_zero 0]
      _ = α * 0 + α * 0 := by rw [left_distrib]
    have g : 0 = α * 0 := Ab.add_cancel_left _ _ _ h
    exact g.symm
  . rw [mul_comm]
    have h : α * 0 + 0 = α * 0 + α * 0 := calc
      α * 0 + 0 = α * 0 := Ab.add_zero _
      _ = α * (0 + 0) := by rw [Ab.add_zero 0]
      _ = α * 0 + α * 0 := by rw [left_distrib]
    have g : 0 = α * 0 := Ab.add_cancel_left _ _ _ h
    exact g.symm
-- (e) $(-1)α = -α$.
theorem Field.mul_neg : (-1) * α = -α := calc
  (-1) * α = (-1) * α + α + -α := by rw [Ab.add_assoc, Ab.add_right_neg, Ab.add_zero]
  _ = (-1 + 1) * α + -α := by rw [right_distrib, mul_comm 1, mul_one]
  _ = -α := by rw [Ab.add_comm (-1), Ab.add_right_neg, mul_comm, (mul_zero α).left, Ab.add_comm, Ab.add_zero]
-- (f) $(-α)(-β) = αβ$.
theorem Field.mul_nnp : -α * -β = α * β := by
  have g : - -β = β := calc
    - -β = - -β + -β + β := by rw [Ab.add_assoc, Ab.add_comm (-β), Ab.add_right_neg, Ab.add_zero]
    _ = β := by rw [Ab.add_comm (- -β), Ab.add_right_neg, Ab.add_comm, Ab.add_zero]
  rw [(mul_neg α).symm, mul_comm (-1), mul_assoc, mul_neg, g]
-- (g)If $αβ = 0$,then either $α = 0$ or $β = 0$ (or both).
theorem Field.mul_zero_either_zero : α * β = 0 → α = 0 ∨ β = 0 := by
  intro h ; sorry
end

/-
2. In familiar systems, such as the integers, we shall almost always use the ordinary operations of addition and multiplication.
  On the rare occasions when we depart from this convention, we shall give ample warning.
  As for "positive," by that word we mean, here and elsewhere in this book, "greater than or equal to zero."
  If 0 is to be excluded, we shall say "strictly positive."
-/
-- (a) Is the set of all positive integers a field?
-- (b) What about the set of all integers?
-- (c) Can the answers to these questions be changed by re-defining addition or multiplication (or both)?

/-
3. Let m be an integer, m ≥ 2, and let ℤₘ, be the set of all positive integers less than m, ℤₘ = {O,1,⋯,m-1}.
  If α and β are in ℤₘ, let α + β be the least positive remainder obtained by dividing the (ordinary) sum of α and β by m, and, similarly, let αβ be the least positive remainder obtained by dividing the (ordinary) product of α and β by m.
  (Example: if m = 12, then 3 + 11 = 2 and 3·11 = 9.)
-/
-- (a) Prove that ℤₘ, is a field if and only if m is a prime.
-- (b) What is -1 in ℤ₅?
-- (c) What is ⅓ in ℤ₇?

/-
4. The example of ℤₚ (where p is a prime) shows that not quite all the laws of elementary arithmetic hold in fields; in ℤ₂, for instance, 1 + 1 = O.
  Prove that if 𝔽 is a field, then either the result of repeatedly adding 1 to itself is always different from 0, or else the first time that it is equal to 0 occurs when the number of summands is a prime.
  (The characteristic of the field 𝔽 is defined to be 0 in the first case and the crucial prime in the second.)
-/

/-
5. Let ℚ(√2) be the set of all real numbers of the form α + β√2, where α and β are rational.
-/
-- (a) Is ℚ(√2) a field?
-- (b) What if α and β are required to be integers?

/-
6. 
-/
-- (a) Does the set of all polynomials with integer coefficients form a field?
-- (b) What if the coefficients are allowed to be real numbers?

/-
6. Let 𝔽 be the set of all (ordered) pairs (α, β) of real numbers.
-/
-- (a) If addition and multiplication are defined by
--   (α, β) + (γ, δ) = (α + γ, β + δ)
-- and
--   (α, β)(γ, δ) = (αγ, βδ),
-- does 𝔽 become a field?

-- (b) If addition and multiplication are defined by
--   (α, β) + (γ, δ) = (α + γ, β + δ)
-- and
--   (α, β)(γ, δ) = (αγ - βδ, αδ + βγ),
-- is 𝔽 a field then?

-- (c) What happens (in both the preceding cases) if we consider ordered pairs of complex numbers instead?
