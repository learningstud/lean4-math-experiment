set_option autoImplicit false

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

structure Uniq {α} (P: α → Prop) (a: α): Prop where
  sat: P a
  uniq (b: α): P b → b = a
-- instance {α} {P: α → Prop} {a: α}: Coe (Uniq P a) (P a) where
--   coe u := u.sat

class Zero (α: Type _) where
  zero: α
@[default_instance] instance {α} [Zero α]: OfNat α (nat_lit 0) where
  ofNat := Zero.zero

class One (α: Type _) where
  one: α
@[default_instance] instance {α} [One α]: OfNat α (nat_lit 1) where
  ofNat := One.one

abbrev Invertible (α) [Zero α] := { a: α // a ≠ 0 }
postfix:arg "ˣ" => Invertible
-- instance {α} [Zero α] {a: α} {nonzero: a ≠ 0}: CoeDep α a αˣ where
--   coe := ⟨a, nonzero⟩

class Inv (α) extends Zero α where
  inv (a: αˣ): αˣ
postfix:arg "⁻¹" => Inv.inv

instance {α} [Add α] [Neg α]: Sub α where
  sub a b := a + -b
instance {α} [Mul α] [Inv α]: HDiv α αˣ α where
  hDiv a b := a * b⁻¹

/-!
# Fields

In what follows we shall have occasion to use various classes of numbers (such as the class of all real numbers or the class of all complex numbers).  Because we should not, at this early stage, commit ourselves to any specific class, we shall adopt the dodge of referring to numbers as scalars.  The reader will not lose anything essential if he consistently interprets scalars as real numbers or as complex numbers; in the examples that we shall study both classes will occur.  To be specific (and also in order to operate at the proper level of generality) we proceed to list all the general facts about scalars that we shall need to assume.

(A) To every pair, $α$ and $β$, of scalars there corresponds a scalar $α + β$, called the *sum* of $α$ and $β$, in such a way that
  (1) addition is commutative, $α + β = β + α$,
  (2) addition is associative, $α + (β + γ) = (α + β) + γ$,
  (3) there exists a unique scalar $0$ (called zero) such that $α + 0 = α$ for every scalar $α$, and
  (4) to every scalar $α$ there corresponds a unique scalar $-α$ such that $α + (-α) = O$.
(B) To every pair, $α$ and $β$, of scalars there corresponds a scalar $αβ$, called the product of $α$ and $β$, in such a way that
  (1) multiplication is commutative, $αβ = βα$,
  (2) multiplication is associative, $α(βγ) = (αβ)γ$,
  (3) there exists a unique non-zero scalar $1$ (called one) such that $α1 = α$ for every scalar $α$, and
  (4) to every non-zero scalar a there corresponds a unique scalar $α⁻¹$ (or $1/a$) such that $αα⁻¹ = 1$.
(C) Multiplication is distributive with respect to addition, $α(β + γ) = αβ + αγ$.

If addition and multiplication are defined within some set of objects (scalars) so that the conditions (A), (B), and (C) are satisfied, then that set (together with the given operations) is called a *field*. Thus, for example, the set $ℚ$ of all rational numbers (with the ordinary definitions of sum and product) is a field, and the same is true of the set $ℝ$ of all real numbers and the set $ℂ$ of all complex numbers.
-/

class Field (Scalar) extends
  Add Scalar, Inv Scalar, Neg Scalar, Mul Scalar, One Scalar
where
  /-
  (A) To every pair, $α$ and $β$, of scalars there corresponds a scalar $α + β$, called the *sum* of $α$ and $β$, in such a way that
  -/
  /--
  (1) addition is commutative, $α + β = β + α$,
  -/
  add_comm (α β: Scalar): α + β = β + α
  /--
  (2) addition is associative, $α + (β + γ) = (α + β) + γ$,
  -/
  add_assoc (α β γ: Scalar): α + (β + γ) = (α + β) + γ
  /--
  (3) there exists a unique scalar $0$ (called zero) such that $α + 0 = α$ for every scalar $α$, and
  -/
  add_zero_uniq: Uniq (∀ α: Scalar, α + . = α) 0
  /--
  (4) to every scalar $α$ there corresponds a unique scalar $-α$ such that $α + (-α) = O$.
  -/
  add_neg_uniq (α: Scalar): Uniq (α + . = 0) (-α)
  /-
  (B) To every pair, $α$ and $β$, of scalars there corresponds a scalar $αβ$, called the product of $α$ and $β$, in such a way that
  -/
  /--
  (1) multiplication is commutative, $αβ = βα$,
  -/
  mul_comm (α β: Scalar): α * β = β * α
  /--
  (2) multiplication is associative, $α(βγ) = (αβ)γ$,
  -/
  mul_assoc (α β γ: Scalar): α * (β * γ) = (α * β) * γ
  /--
  (3) there exists a unique non-zero scalar $1$ (called one) such that $α1 = α$ for every scalar $α$, and
  -/
  mul_one_uniq: Uniq (∀ α: Scalar, α * . = α) 1
  /--
  (4) to every non-zero scalar a there corresponds a unique scalar $α⁻¹$ (or $1/a$) such that $αα⁻¹ = 1$.
  -/
  mul_inv_uniq (α: Scalarˣ): Uniq (α.val * . = 1) α⁻¹
  /--
  (C) Multiplication is distributive with respect to addition, $α(β + γ) = αβ + αγ$.
  -/
  left_distrib (α β γ: Scalar): α * (β + γ) = α * β + α * γ

namespace Field
  variable {𝔽} [field: Field 𝔽]

  abbrev add_zero := field.add_zero_uniq.sat
  abbrev add_neg (α: 𝔽) := (field.add_neg_uniq α).sat
  abbrev mul_one := field.mul_one_uniq.sat
  abbrev mul_inv (α: 𝔽) {nonzero: α ≠ 0} :=
    (field.mul_inv_uniq ⟨α, nonzero⟩).sat
end Field

/-!
## Excercises
-/

namespace Field
/-!
1. Almost all the laws of elementary arithmetic are consequences of the axioms defining a field.  Prove, in particular, that if $𝔽$ is a field, and if $α$, $β$, and $γ$ belong to $𝔽$, then the following relations hold.
-/
variable {𝔽} [Field 𝔽] (α β γ: 𝔽)

/--
(a) $0 + α = α$.
-/
theorem zero_add: 0 + α = α :=
  by rw [add_comm, add_zero]

/--
(b) If $α + β = α + γ$, then $β = γ$.
-/
theorem cancel_add: α + β = α + γ → β = γ :=
  by intros h ; rw [aux β, aux γ] ; exact congrArg (-α + .) h
where aux δ: δ = -α + (α + δ) :=
    by rw [add_assoc, add_comm (-α), add_neg, zero_add]

/--
(c) $α + (β - α) = β$. (Here $β - α = β + (-α)$.)
-/
theorem add_222: α + (β - α) = β := -- type (2,2,2) algebra as a quasigroup
  have: β - α = β + -α := rfl
  by rw [this, add_comm β, add_assoc, add_neg, zero_add]

/--
(d) $α·0 = 0·α = 0$. (For clarity or emphasis we sometimes use the dot to indicate multiplication.)
-/
protected theorem mul_zero_zero_mul: α * 0 = 0 ∧ 0 * α = 0 :=
  suffices α * 0 = 0 from ⟨this, mul_comm 0 α ▸ this⟩
  suffices α * 0 + α * 0 = α * 0 + 0 from cancel_add _ _ _ this
  by rw [←left_distrib, add_zero, add_zero]

abbrev mul_zero := (Field.mul_zero_zero_mul α).left
abbrev zero_mul := (Field.mul_zero_zero_mul α).right

/--
(e) $(-1)α = -α$.
-/
theorem neg_mul: (-1) * α = -α :=
  suffices α + (-1) * α = 0 from (add_neg_uniq α).uniq _ this
  calc  _ = α * 1 + (-1) * α := by rw [mul_one]
        _ = 0 := by rw [mul_comm (-1), ←left_distrib, add_neg, mul_zero]

/--
(f) $(-α)(-β) = αβ$.
-/
theorem neg_mul_neg: -α * -β = α * β :=
  have: - -β = β := calc
    _ = - -β + -β + β := by rw [←add_assoc, add_comm (-β), add_neg, add_zero]
    _ = β := by rw [add_comm (- -β), add_neg, zero_add]
  by rw [←neg_mul α, mul_comm (-1), ←mul_assoc, neg_mul, this]

/--
(g)If $αβ = 0$,then either $α = 0$ or $β = 0$ (or both).
-/
theorem integral_domain: α * β = 0 → α = 0 ∨ β = 0 := by
  intros h ; by_cases g: α = 0
  . case inl => exact .inl g
  . apply Or.inr ; let «α⁻¹» := ⟨α, g⟩⁻¹ ; have h := congrArg («α⁻¹».val * .) h
    simp at h ; rw [mul_zero, mul_assoc, mul_comm «α⁻¹».val, mul_inv] at h
    rw [←h, mul_comm, mul_one]

end Field


/-!
2. In familiar systems, such as the integers, we shall almost always use the ordinary operations of addition and multiplication.  On the rare occasions when we depart from this convention, we shall give ample warning.  As for "positive," by that word we mean, here and elsewhere in this book, "greater than or equal to zero."  If 0 is to be excluded, we shall say "strictly positive."
-/
-- (a) Is the set of all positive integers a field?
-- (b) What about the set of all integers?
-- (c) Can the answers to these questions be changed by re-defining addition or multiplication (or both)?

/-!
3. Let m be an integer, m ≥ 2, and let ℤₘ, be the set of all positive integers less than m, ℤₘ = {O,1,⋯,m-1}.  If α and β are in ℤₘ, let α + β be the least positive remainder obtained by dividing the (ordinary) sum of α and β by m, and, similarly, let αβ be the least positive remainder obtained by dividing the (ordinary) product of α and β by m.  (Example: if m = 12, then 3 + 11 = 2 and 3·11 = 9.)
-/
-- (a) Prove that ℤₘ, is a field if and only if m is a prime.
-- (b) What is -1 in ℤ₅?
-- (c) What is ⅓ in ℤ₇?

/-!
4. The example of ℤₚ (where p is a prime) shows that not quite all the laws of elementary arithmetic hold in fields; in ℤ₂, for instance, 1 + 1 = O.  Prove that if 𝔽 is a field, then either the result of repeatedly adding 1 to itself is always different from 0, or else the first time that it is equal to 0 occurs when the number of summands is a prime.  (The characteristic of the field 𝔽 is defined to be 0 in the first case and the crucial prime in the second.)
-/

/-!
5. Let ℚ(√2) be the set of all real numbers of the form α + β√2, where α and β are rational.
-/
-- (a) Is ℚ(√2) a field?
-- (b) What if α and β are required to be integers?

/-!
6. 
-/
-- (a) Does the set of all polynomials with integer coefficients form a field?
-- (b) What if the coefficients are allowed to be real numbers?

/-!
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
