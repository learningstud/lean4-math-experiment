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

/-! ## I 3.2 The field axioms -/

axiom ℝ: Type
namespace ℝ
  protected axiom sum: ℝ → ℝ → ℝ
  noncomputable instance: Add ℝ where add := ℝ.sum

  protected axiom product: ℝ → ℝ → ℝ
  noncomputable instance: Mul ℝ where mul := ℝ.product

  variable (x y z: ℝ)
  /-- Axiom 1. Commutative laws. -/
  protected axiom comm: x + y = y + x ∧ x⬝y = y⬝x
  /-- Axiom 2. Associative laws. -/
  protected axiom assoc: x + (y + z) = (x + y) + z ∧ x⬝(y⬝z) = (x⬝y)⬝z
  /-- Axiom 3. Distributive law. -/
  protected axiom distrib: x⬝(y + z) = x⬝y + x⬝z
  /-- Axiom 4. Existence of identity elements. -/
  protected axiom zero: ℝ
  @[default_instance] noncomputable instance: Zero ℝ where zero := ℝ.zero
  /-- Axiom 4. Existence of identity elements. -/
  protected axiom one: ℝ
  @[default_instance] noncomputable instance: One ℝ where one := ℝ.one
  /-- Axiom 4. Existence of identity elements. -/
  protected axiom identities: 0 ≠ 1 ∧ ∀ x: ℝ, x + 0 = x ∧ 1⬝x = x
  /-- Axiom 5. Existence of negatives. -/
  protected axiom negatives: ∀ x: ℝ, ∃ y: ℝ, x + y = 0
  /-- Axiom 6. Existence of reciprocals. -/
  protected axiom reciprocals: ∀ x: ℝ, x ≠ 0 → ∃ y: ℝ, x⬝y = 1



  variable (a b c d: ℝ)

  theorem zero_add: 0 + a = a := sorry

  /-- Theorem I.1. Cancellation law for addition. -/
  theorem cancel_add: a + b = a + c → b = c := sorry

  protected axiom subtraction: ℝ → ℝ → ℝ
  noncomputable instance: Sub ℝ where sub := ℝ.subtraction
  /-- Theorem I.2. Possibility of subtraction. -/
  theorem sub_uniq (a b: ℝ): Uniq (a + . = b) (b - a) := sorry
  noncomputable instance: Neg ℝ where neg a := 0 - a

  /-- Theorem I.3. -/
  theorem add_neg: b - a = b + -a := sorry

  /-- Theorem I.4. -/
  theorem neg_neg: -(-a) = a := sorry

  /-! ## I 3.3 Exercises -/

  /-- Theorem I.5. -/
  theorem mul_sub: a⬝(b - c) = a⬝b - a⬝c := sorry

  /-- Theorem I.6. -/
  theorem zero_mul: 0 * a = 0 := sorry
  /-- Theorem I.6. -/
  theorem mul_zero: a⬝0 = 0 := sorry

  /-- Theorem I.7. Cancellation law for multiplication. -/
  theorem cancel_mul: a⬝b = a⬝c ∧ a ≠ 0 → b = c := sorry
  theorem one_uniq: Uniq (∀ x: ℝ, . * x = x) 1 := sorry

  protected axiom quotient: ℝ → ℝˣ → ℝ
  noncomputable instance: HDiv ℝ ℝˣ ℝ where hDiv := ℝ.quotient
  /-- Theorem I.8. Possibility of division. -/
  theorem div_uniq (a: ℝˣ) (b: ℝ): Uniq (a * . = b) (b/a) := sorry
  noncomputable instance: Inv ℝ where inv a := ⟨1 / a, sorry⟩

  /-- Theorem I.9. -/
  theorem mul_inv (a: ℝˣ): b/a = b⬝a⁻¹ := sorry

  /-- Theorem I.10. -/
  theorem inv_inv (a: ℝˣ): a⁻¹⁻¹ = a := sorry

  /-- Theorem I.11. -/
  theorem integral_domain: a⬝b = 0 → a = 0 ∨ b = 0 := sorry

  /-- Theorem I.12. -/
  theorem neg_mul: (-a)⬝b = -(a⬝b) := sorry
  /-- Theorem I.12. -/
  theorem neg_mul_neg: (-a)⬝(-b) = a⬝b := sorry

  noncomputable instance: Mul ℝˣ where mul a b := ⟨a.val * b.val, sorry⟩

  /-- Theorem I.13. -/
  theorem div_add_div (b d: ℝˣ): a/b + c/d = (a⬝d + b⬝c)/(b⬝d) := sorry

  /-- Theorem I.14. -/
  theorem div_mul_div (b d: ℝˣ): (a/b)⬝(c/d) = (a⬝c)/(b⬝d) := sorry

  noncomputable instance: Div ℝˣ where div a b := ⟨a.val / b, sorry⟩
  /-- Theorem I.15. -/
  theorem div_div_div (b c d: ℝˣ): (a/b)/(c/d) = (a⬝d)/(b⬝c) := sorry

  theorem neg_zero: -0 = 0 := sorry
  theorem one_inv: ⟨1, sorry⟩⁻¹.val = 1 := sorry
  theorem zero_not_inv: 0⬝a ≠ 1 := sorry
  theorem neg_add: -(a + b) = -a - b := sorry
  theorem neg_sub: -(a - b) = -a + b := sorry
  theorem sub_add_sub: (a - b) + (b - c) = a - c := sorry
  theorem inv_mul_inv (a b: ℝˣ): (a⬝b)⁻¹ = a⁻¹⬝b⁻¹ := sorry
  theorem neg_div (b: ℝˣ): (-a)/b = -(a/b) := sorry
  instance: Neg ℝˣ where neg := sorry
  theorem div_neg (b: ℝˣ): a/(-b) = -(a/b) := sorry
  theorem div_sub_div (b d: ℝˣ): a/b - c/d = (a⬝d - b⬝c)/(b⬝d) := sorry



  /-! ## I 3.4 The order axioms -/

  /-- Positiveness. -/
  protected axiom positive: ℝ → Prop
  /-- Axiom 7. -/
  protected axiom pos_closure: x.positive ∧ y.positive → (x + y).positive ∧ (x⬝y).positive
  /-- Axiom 8. -/
  protected axiom pos_dichotomy: x ≠ 0 → (x.positive ∨ (-x).positive) ∧ ¬(x.positive ∧ (-x).positive)
  /-- Axiom 9. -/
  protected axiom zero_not_pos: ¬ℝ.positive 0

  instance: LT ℝ where lt x y := (y - x).positive
  instance: LE ℝ where le x y := x < y ∨ x = y

  /-- Theorem I.16. Trichotomy law. FIXME -/
  theorem trichotomy: a < b ∨ b < a ∨ a = b := sorry
  /-- Theorem I.17. Transitive law. -/
  theorem lt_trans: a < b → b < c → a < c := sorry
  /-- Theorem I.18. -/
  theorem add_lt_add: a < b → a + c < b + c := sorry
  /-- Theorem I.19. -/
  theorem mul_lt_mul: a < b → c > 0 → a⬝c < b⬝c := sorry
  
  protected noncomputable abbrev square (x: ℝ): ℝ := x⬝x
  postfix:arg "²" => ℝ.square
  /-- Theorem I.20. -/
  theorem pos_square: a ≠ 0 → a² > 0 := sorry
  /-- Theorem I.21. -/
  theorem zero_lt_one: 0 < 1 := sorry

  /-! ## I 3.5 Exercises -/

  /-- Theorem I.22. -/
  example: a < b → c < 0 → a⬝c > b⬝c := sorry
  /-- Theorem I.23. -/
  example: a < b → -a > -b := sorry
  /-- Theorem I.23. -/
  example: a < 0 → -a > 0 := sorry
  /-- Theorem I.24. -/
  example: a⬝b > 0 → (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) := sorry
  /-- Theorem I.25. -/
  example: a < c → b < d → a + b < c + d := sorry

  example: ∀ x: ℝ, x² + 1 ≠ 0 := sorry
  example: a < 0 → b < 0 → a + b < 0 := sorry
  example: (a > 0 → 1/a > 0) ∧ (a < 0 → 1/a < 0) := sorry
  example: 0 < a → a < b → 0 < b⁻¹ ∧ b⁻¹ < a⁻¹ := sorry
  theorem le_trans: a ≤ b → b ≤ c → a ≤ c := sorry
  example: a ≤ b → b ≤ c → a = c → b = c := sorry
  example: (a² + b² ≥ 0) ∧ (¬(a = 0 ∧ b = 0) → a² + b² > 0) := sorry
  example: ∀ a: ℝ, ¬∀ x: ℝ, x ≤ a := sorry
  example: (∀ h: ℝ, 0 ≤ x ∧ x < h) → x = 0 := sorry
end ℝ

/-- Positive numbers. -/
abbrev «ℝ⁺» := Subtype ℝ.positive

/-! ## 1 3.6 Integers and rational numbers -/
protected inductive ℝ.inductive: ℝ → Prop
  | one: ℝ.inductive 1
  | succ {x: ℝ}: x.inductive → (x + 1).inductive 
