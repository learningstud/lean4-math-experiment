set_option autoImplicit false

@[inherit_doc] infixl:70 "⬝"   => HMul.hMul
macro_rules | `($x ⬝ $y)   => `(binop% HMul.hMul $x $y)

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

class Field (α) extends Add α, Mul α, Zero α, One α, Sub α, HDiv α αˣ α where
  add_comm (x y: α): x + y = y + x
  mul_comm (x y: α): x * y = y * x

  add_assoc (x y z: α): x + (y + z) = (x + y) + z
  mul_assoc (x y z: α): x * (y * z) = (x * y) * z

  /-- Axiom 3. Distributive law. Left distributivity. -/
  mul_add (x y z: α): x⬝(y + z) = x⬝y + x⬝z

  zero_ne_one: zero ≠ one
  add_zero (x: α): x + 0 = x
  one_mul (x: α): 1⬝x = x

  /-- Axiom 5. Existence of negatives. -/
  protected exists_neg: ∀ x: α, ∃ y: α, x + y = 0

  /-- Axiom 6. Existence of reciprocals. -/
  protected exists_inv: ∀ x: α, x ≠ 0 → ∃ y: α, x⬝y = 1

namespace Field
  variable {α} [Field α] (a b c d: α)

  theorem zero_add: 0 + a = a :=
    by rw [add_comm, add_zero]

  /-- Theorem I.1. Cancellation law for addition. -/
  theorem cancel_add: a + b = a + c → b = c :=
    let ⟨«-a», a_add_neg⟩ := Field.exists_neg a
    let aux (d: α): d = «-a» + (a + d) :=
      by rw [add_assoc, add_comm «-a», a_add_neg, zero_add]
    fun h => by rw [aux b, aux c] ; exact congrArg («-a» + .) h
  
  /-- Theorem I.2. Possibility of subtraction. -/
  theorem sub_uniq (a b: α): Uniq (a + . = b) (b - a) := sorry
  instance: Neg α where neg a := 0 - a

  theorem add_neg: b - a = b + -a := sorry

  theorem neg_neg: -(-a) = a := sorry

  theorem mul_sub: a⬝(b - c) = a⬝b - a⬝c := sorry

  theorem mul_zero: a⬝0 = 0 :=
    suffices a⬝0 + a⬝0 = a⬝0 + 0 from cancel_add _ _ _ this
    by rw [←mul_add, add_zero, add_zero]
  theorem zero_mul: 0 * a = 0 :=
    by rw [mul_comm, mul_zero]

  theorem cancel_mul: a⬝b = a⬝c ∧ a ≠ 0 → b = c := sorry
  theorem one_uniq: Uniq (∀ x: α, . * x = x) 1 := sorry

  theorem div_uniq (a: αˣ) (b: α): Uniq (a * . = b) (b/a) := sorry
  instance: Inv α where inv a := ⟨(1:α) / a, sorry⟩

  theorem mul_inv (a: αˣ): b/a = b⬝a⁻¹ := sorry

  theorem inv_inv (a: αˣ): a⁻¹⁻¹ = a := sorry

  theorem integral_domain: a⬝b = 0 → a = 0 ∨ b = 0 := by
    intros h ; by_cases g: a = 0
    . case inl => exact .inl g
    . apply Or.inr
      let «a⁻¹» := ⟨a, g⟩⁻¹ ; have h := congrArg («a⁻¹».val * .) h
      simp at h ; rw [mul_zero, mul_assoc, mul_comm «a⁻¹».val, mul_inv] at h
      rw [←h, mul_comm, mul_one]
  
  theorem neg_mul: (-a)⬝b = -(a⬝b) := sorry

  theorem neg_mul_neg: (-a)⬝(-b) = a⬝b := sorry

  instance: Mul αˣ where mul a b := ⟨a.val * b.val, sorry⟩
  theorem div_add_div (b d: αˣ): a/b + c/d = (a⬝d + b⬝c) / (b⬝d) := sorry

  theorem div_mul_div (b d: αˣ): (a/b)⬝(c/d) = (a⬝c)/(b⬝d) := sorry

  instance: Div αˣ where div a b := ⟨a.val / b, sorry⟩
  theorem div_div_div (b c d: αˣ): (a/b)/(c/d) = (a⬝d)/(b⬝c) := sorry

  -- theorem neg_mul: (-1) * α = -α :=
  --   suffices α + (-1) * α = 0 from (add_neg_uniq α).uniq _ this
  --   calc  _ = α * 1 + (-1) * α := by rw [mul_one]
  --         _ = 0 := by rw [mul_comm (-1), ←left_distrib, add_neg, mul_zero]

  -- theorem neg_mul_neg: -α * -β = α * β :=
  --   have: - -β = β := calc
  --     _ = - -β + -β + β := by rw [←add_assoc, add_comm (-β), add_neg, add_zero]
  --     _ = β := by rw [add_comm (- -β), add_neg, zero_add]
  --   by rw [←neg_mul α, mul_comm (-1), ←mul_assoc, neg_mul, this]


end Field

