/-!
# Chapter 2. Homotopy type theory

- [ground_zero](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/Types/Id.lean)
-/

#check Eq
inductive Path {A: Type u}: A → A → Type u
  | refl {x: A}: Path x x
@[inherit_doc] infix:50 (priority := high) " = " => Path
-- @[match_pattern] def Path.rfl.{u} {A: Type u} {x: A} := Path.refl x
#check_failure refl
export Path (refl)

section
  variable {A: Type u} (D: (x y: A) → x = y → Type v) (d: (a: A) → D a a refl)
  def Path.ind (x y: A): (p: x = y) → D x y p
    | refl => d x
  theorem «2.0.1» (a: A): Path.ind D d a a refl = d a
    := refl
end


/-! ## 2.1 Types are higher groupoids -/

/-- Lemma 2.1.1 -/
protected def Path.inv: (x = y) → (y = x)
  | refl => refl
@[inherit_doc] postfix:arg "⁻¹" => Path.inv
#reduce refl⁻¹

/-- Lemma 2.1.2 -/
protected def Path.concat: (x = y) → (y = z) → (x = z)
  | refl, refl => refl
@[inherit_doc] infixl:60 " ⬝ " => Path.concat
#reduce refl ⬝ refl

/-- `calc` requires `Trans` to be implemented for `_` on the LHS to work -/
instance: Trans (@Path A) Path Path where
  trans := Path.concat

section «Lemma 2.1.4»

  /-- Lemma 2.1.4 (ⅰ) -/
  def Path.con_refl: {p: x = y} → p = p ⬝ refl
    | refl => refl
  /-- Lemma 2.1.4 (ⅰ) -/
  def Path.refl_con: {p: x = y} → p = refl ⬝ p
    | refl => refl
  /-- Lemma 2.1.4 (ⅱ) -/
  def Path.inv_con: {p: x = y} → p⁻¹ ⬝ p = refl
    | refl => refl
  /-- Lemma 2.1.4 (ⅱ) -/
  def Path.con_inv: {p: x = y} → p ⬝ p⁻¹ = refl
    | refl => refl
  /-- Lemma 2.1.4 (ⅲ) -/
  def Path.inv_inv: {p: x = y} → p⁻¹⁻¹ = p
    | refl => refl
  /-- Lemma 2.1.4 (ⅳ) -/
  def Path.con_assoc: {p: a = b} → {q: b = c} → {r: c = d} → (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r)
    | refl, refl, refl => refl

  /-! ### Extras -/
  def Path.con_comm_refl: {p: x = y} → p ⬝ refl = refl ⬝ p
    | refl => refl
  def Path.con_cancel: {p p': x = y} → {q: y = z} → p ⬝ q = p' ⬝ q → p = p'
    | refl, refl, _, _ => refl
  def Path.inv_con_inv: {p: x = y} → {q: y = z} → (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹
    | refl, refl => refl
  
  def Path.inv_op: {p: x = y} → {q: y = x} → p⁻¹ = q → p = q⁻¹
    | refl, refl, _ => refl -- | _, _, refl => inv_inv⁻¹
  def Path.op_inv {p: x = y}: {q: y = x} → p = q⁻¹ → p⁻¹ = q
    | refl, refl => refl

  def Path.refl_con_refl: {p: x = y} → p = refl ⬝ p ⬝ refl
    | refl => refl  
  
end «Lemma 2.1.4»

section «Theorem 2.1.6»

  /-- Right whiskering by induction on `r` -/
  def Path.right_whiskering {p q: a = b} (α: p = q) (r: b = c): p ⬝ r = q ⬝ r :=
    α.casesOn refl -- r.casesOn (p.con_refl⁻¹ ⬝ α ⬝ q.con_refl)
  @[inherit_doc] infix:60 " ⬝ᵣ " => Path.right_whiskering

  /-- Left whiskering by induction on `r`

  NOTE: Important technique!
  -/
  def Path.left_whiskering (q: a = b) {r s: b = c} (β: r = s): q ⬝ r = q ⬝ s :=
    β.casesOn refl -- match q, r, s with | refl, r, s => r.refl_con⁻¹ ⬝ β ⬝ s.refl_con
  @[inherit_doc] infix:60 " ⬝ₗ " => Path.left_whiskering

  abbrev Loop (a: A) := Path a a
  abbrev Loop2 (a: A) := Loop (@refl A a)

  -- section
  --   variable {p q: a = b} {r s: b = c} (α: p = q) (β: r = s)
  --   def horizontalComposition := (α ⬝ᵣ r) ⬝ (q ⬝ₗ β)
  --   infix:60 " ★ " => horizontalComposition
  --   def horizontalComposition' := (p ⬝ₗ β) ⬝ (α ⬝ᵣ s)
  --   infix:60 " ★' " => horizontalComposition'
  --   def comp_unique: α ★ β = α ★' β :=
  --     match α, β with | refl, refl => match p, r with | refl, refl => refl
  -- end

  def «Eckmann-Hilton»: (α β: Loop2 a) → α ⬝ β = β ⬝ α
    | refl, refl => refl
  -- def «Eckmann-Hilton» (α β: Loop2 a): α ⬝ β = β ⬝ α :=
  --   calc α ⬝ β
  --     = α ★ β := .refl_con_refl ★ .refl_con_refl
  --   _ = α ★' β := match α, β with | refl, refl => refl -- comp_unique α β
  --   _ = β ⬝ α := (.refl_con_refl ★ .refl_con_refl)⁻¹

end «Theorem 2.1.6»

section «Definition 2.1.7»
  structure PointedType where
    carrier: Type u
    basepoint: carrier
  instance: CoeSort PointedType (Type u) where
    coe P := P.carrier
end «Definition 2.1.7»

section «Definition 2.1.8»
  abbrev LoopSpace (P: PointedType) :=
    let a := P.basepoint
    PointedType.mk (a = a) refl
  def Ω (n: Nat) (P: PointedType): PointedType :=
    match n with
    | 0 => P
    | .succ n => Ω n (LoopSpace P)
end «Definition 2.1.8»

/- The following won't work due to Coq not supporting induction-recursion!

section «Definition 2.1.8»
  abbrev LoopSpace.{u} {A: Type u} (P: PointedType A) :=
    PointedType.mk (@refl _ P.basepoint)
  section
    universe u
    variable {A: Type u} (P: PointedType A)
    #check LoopSpace P
    #check LoopSpace <| LoopSpace P
    #check LoopSpace <| LoopSpace <| LoopSpace P
    #reduce LoopSpace <| LoopSpace <| LoopSpace P
  end
  mutual
    def T.{u} (n: Nat) {A: Type u} (P: PointedType A): Type u :=
      match n with
      | 0 => PointedType A
      -- | 1 => PointedType (P.basepoint = P.basepoint)
      -- | 2 => PointedType ((LoopSpace P).basepoint = (LoopSpace P).basepoint)
      -- | 3 => PointedType ((LoopSpace (LoopSpace P)).basepoint = (LoopSpace (LoopSpace P)).basepoint)
      | .succ n => let ⟨a⟩ := Ω n P ; PointedType (a = a)
    def Ω.{u} (n: Nat) {A: Type u} (P: PointedType A): (T n P) :=
      match n with
      | 0 => P
      | .succ n => Ω n (LoopSpace P)
  end
end «Definition 2.1.8»
-/

/-! ## 2.2 Functions are functors -/

/-- Lemma 2.2.1 -/
def ap (f: A → B): x = y → f x = f y
  | refl => refl

/-
-- BAD:
instance {A: Sort u} {B: Sort v}: CoeFun (A → B) (fun (f: A → B) => {x y: A} → x = y → f x = f y) where
  coe f := ap f
example (f: A → B) {x: A}: f (Refl x) = Refl (f x) :=
  refl
-- GOOD:
instance {A: Sort u} {B: Sort v} (f: A → B) {x y: A}: CoeDep (A → B) f (x = y → f x = f y) where
  coe p := ap f p
example (f: A → B) {x: A}: (f: x = x → f x = f x) (Refl x) = Refl (f x) :=
  refl
-/

section «Lemma 2.2.2»
  variable {f: A → B} {g: B → C}

  /-- Lemma 2.2.2 (ⅰ) -/
  example: {p: x = y} → {q: y = z} → ap f (p ⬝ q) = ap f p ⬝ ap f q
    | refl, refl => refl -- := q.casesOn (p.casesOn refl)
  /-- Lemma 2.2.2 (ⅱ) -/
  example: {p: x = y} → ap f p⁻¹ = (ap f p)⁻¹
    | refl => refl
  /-- Lemma 2.2.2 (ⅲ) -/
  example: {p: x = y} → ap g (ap f p) = ap (g ∘ f) p
    | refl => refl
  /-- Lemma 2.2.2 (ⅳ) -/
  def Path.ap_id: {p: x = y} → ap id p = p
    | refl => refl
  
end «Lemma 2.2.2»

/-! ## 2.3 Type families are fibrations -/

section «Lemma 2.3.1»
  /-- Lemma 2.3.1; there is no unicode subscript `*`, so I use `+` instead. -/
  def Path.transport (P: A → _) {x y: A}: (x = y) → P x → P y
    | refl => id
  export Path (transport) -- `transportᴾ(p,-): P(x) → P(y)` is used often.
  abbrev Path.Transport {P: A → _} {x y: A} := @transport A P x y
  @[inherit_doc] postfix:max "₊" => Path.Transport
end «Lemma 2.3.1»

section «Lemma 2.3.2»
  variable {P: A → _} {x y: A} (u: P x) (p: x = y)
  /-- Lemma 2.3.2 -/
  def Path.lift: Sigma.mk x u = ⟨y, (p₊ u)⟩ :=
    p.casesOn refl
  export Path (lift)
  #reduce ap Sigma.fst (lift u refl) -- refl
  example: ap Sigma.fst (lift u refl) = refl := refl
  example: ap Sigma.fst (lift u p) = p := p.casesOn refl
end «Lemma 2.3.2»

/-- Lemma 2.3.4 -/
def apd {P: A → _} (f: (x: A) → P x): (p: x = y) → p₊ (f x) = f y
  | refl => refl
#print ap

/-- Lemma 2.3.5 -/
def transportconst {A: Type u} {x y: A} (B: Type v) (p: x = y) (b: B):
  transport (fun _ => B) p b = b
:= p.casesOn refl

def «Lemma 2.3.8» {A: Type u} {x y: A} {B: Type v} (f: A → B) (p: x = y):
  apd f p = transportconst B p (f x) ⬝ ap f p
:= p.casesOn refl

def «Lemma 2.3.9» {P: A → _} {p: x = y} {q: y = z} {u: P x}:
  q₊ (p₊ u) = (p ⬝ q)₊ u
:= q.casesOn (p.casesOn refl)

def «Lemma 2.3.10» {f: A → B} {P: B → _} {p: x = y} {u: P (f x)}:
  transport (P ∘ f) p u = transport P (ap f p) u
:= p.casesOn refl

def «Lemma 2.3.11» {P Q: A → _} {f: (x: A) → P x → Q x} {p: x = y} {u: P x}:
  transport Q p (f x u) = f y (transport P p u)
:= p.casesOn refl

/-! ## 2.4 Homotopies and equivalences -/

/-- Definition 2.4.1 (Homotopy). `abbrev` or `def`? -/
abbrev Homotopy {P: A → _} (f g: (x: A) → P x) := (x: A) → f x = g x
/- Is 50 the appropriate precedence? -/
@[inherit_doc] infix:50 " ~ " => Homotopy

section «Lemma 2.4.2»
  variable {A: Type u} {P: A → Type v} {f g h: (x: A) → P x}
  def Homotopy.refl: f ~ f
    | _ => Path.refl
  def Homotopy.symm: f ~ g → g ~ f
    | p, x => (p x)⁻¹
  def Homotopy.trans: f ~ g → g ~ h → f ~ h
    | p, q, x => p x ⬝ q x
end «Lemma 2.4.2»

def «Lemma 2.4.3» {f g: A → B} (H: f ~ g) {x y: A} (p: x = y):
  H x ⬝ ap g p = ap f p ⬝ H y
:= p.casesOn (H x).con_comm_refl

def «Corollary 2.4.4» {f: A → A} (H: f ~ id) (x: A): H (f x) = ap f (H x) :=
  Path.con_cancel <| calc H (f x) ⬝ H x
                        = H (f x) ⬝ ap id (H x) := _ ⬝ₗ .ap_id⁻¹
                      _ = ap f (H x) ⬝ H x      := «Lemma 2.4.3» _ _

/-- Definition 2.4.6 --/
structure qinv (f: A → B) := (g: B → A) (α: f ∘ g ~ id) (β: g ∘ f ~ id)

/-- Example 2.4.7 --/
protected def qinv.refl: qinv (@id A) := ⟨id, @refl _, @refl _⟩

section «Example 2.4.8»
  variable {x y z: A} (p: x = y)
  example: qinv ((p ⬝ ·): (y = z) → (x = z)) where
    g r := p⁻¹ ⬝ r
    α | refl => p.casesOn refl
    β | refl => p.casesOn refl
  example: qinv ((· ⬝ p): (z = x) → (z = y)) :=
    ⟨(· ⬝ p⁻¹), p.casesOn fun | refl => refl, p.casesOn fun | refl => refl⟩
end «Example 2.4.8»

section «Example 2.4.9»
  variable {x y: A} (p: x = y) (P: A → Type _)
  example: qinv ((transport P p ·): P x → P y) where
    g := (transport P p⁻¹ ·)
    α := p.casesOn (@refl _)
    β := p.casesOn (@refl _)
end «Example 2.4.9»

section «Definition 2.4.10»
  structure isequiv (f: A → B) where
    g: B → A
    α: f ∘ g ~ id
    h: B → A
    β: h ∘ f ~ id 
  def qinv_is_isequiv (f: A → B): qinv f → isequiv f
    | ⟨g, α, β⟩ => ⟨g, α, g, β⟩
  def isequiv_is_qinv (f: A → B): isequiv f → qinv f
    | ⟨g, α, h, β⟩ =>
        let γ (x: B) := (β (g x))⁻¹ ⬝ ap h (α x)
        ⟨g, α, fun x => γ (f x) ⬝ β x⟩
  -- example (f: A → B): (e₁ e₂: isequiv f) → e₁ = e₂
  --   | ⟨g₁, α₁, h₁, β₁⟩, ⟨g₂, α₂, h₂, β₂⟩ =>
  --     have: f ∘ g₁ ~ f ∘ g₂ := α₁.trans α₂.symm
  --     sorry
end «Definition 2.4.10»

/-- Definition 2.4.11: Type equivalence -/
def equiv (A: Type u) (B: Type v) := (f: A → B) × isequiv f
@[inherit_doc] infix:50 " ≃ " => equiv

section «Lemma 2.4.12»
  variable {f: A → B}
  local instance: Coe (qinv f) (isequiv f) where
    coe := qinv_is_isequiv f
  local instance: Coe (isequiv f) (qinv f) where
    coe := isequiv_is_qinv f
  local instance: Coe (isequiv f) (equiv A B) where
    coe e := ⟨f, e⟩
  example: qinv f → equiv A B
    | e => e -- | ⟨g, p, q⟩ => ⟨f, ⟨g, p⟩, g, q⟩

  /-- Lemma 2.4.12 (ⅰ) -/
  example: A ≃ A :=
    @qinv.refl A
  /-- Lemma 2.4.12 (ⅱ) -/
  example: A ≃ B → B ≃ A
    | ⟨f, e⟩ => let ⟨g, p, q⟩: qinv f := e ; (⟨f, q, p⟩: qinv g)
    -- | ⟨f, e⟩ => let ⟨g, p, q⟩: qinv f := e ; (⟨f, q, p⟩: qinv g)
  /-- Lemma 2.4.12 (ⅲ) -/
  example: A ≃ B → B ≃ C → A ≃ C
    | ⟨f₁, e₁⟩, ⟨f₂, e₂⟩ =>
      let ⟨g₁, p₁, q₁⟩: qinv f₁ := e₁
      let ⟨g₂, p₂, q₂⟩: qinv f₂ := e₂
      show qinv (f₂ ∘ f₁) from {
        g := g₁ ∘ g₂
        α := fun x => ap f₂ (p₁ (g₂ x)) ⬝ p₂ x
        β := fun x => ap g₁ (q₂ (f₁ x)) ⬝ q₁ x
      }
end «Lemma 2.4.12»

/-! ## 2.5 The higher groupoid structure of type formers -/

/-- Formula 2.5.1 -/
example (b b': B) (c c': C): ((b, c) = (b', c')) ≃ (b = b' × c = c') :=
  sorry

/-! ## 2.6 Cartesian product types -/

def «2.6.1» (x y: A × B): (x = y) → (x.1 = y.1) × (x.2 = y.2)
  | refl => (refl, refl)

/-- 2.6.2 -/
def «2.6.2»: (x y: A × B) → qinv («2.6.1» x y)
  | (a, b), (a', b') => by simp ; exact {
    g := fun | (refl, refl) => refl
    α := fun | (refl, refl) => refl
    β := fun | refl => refl
  }
/-- 2.6.3 -/
def «pair⁼» {x y: A × B} := («2.6.2» x y).1

def «2.6.4» {A B: Z → _} {z w: Z} (p: z = w) {x: A z × B z}:
  transport (fun z => A z × B z) p x = (p₊ x.1, p₊ x.2)
:= p.casesOn refl

/-! ## 2.7 Σ-Types -/

def «2.7.2» {P: A → _} (w w': Σ x: A, P x):
  (w = w') ≃ Σ p: w.1 = w'.1, p₊ (w.2) = w'.2
:=
by constructor
   case fst => exact fun | refl => ⟨refl, refl⟩
   case snd => exact qinv_is_isequiv _ (
     match w, w' with
     | ⟨x, y⟩, ⟨x', y'⟩ => by simp ; exact {
        g := fun | ⟨p, q⟩ => match p, q with | refl, refl => refl -- q.casesOn (p.casesOn refl)
        α := fun | ⟨p, q⟩ => q.casesOn (p.casesOn refl)
        β := fun | refl => refl
    }
  )

def «2.7.3» {P: A → _} (z: Σ x: A, P x): z = ⟨z.1, z.2⟩ :=
  («2.7.2» z ⟨z.1, z.2⟩).2.1 ⟨refl, refl⟩

instance: Coe (Prod A B) (Sigma fun (_: A) => B) where
  coe p := ⟨p.1, p.2⟩

-- #check Sigma
-- def «2.7.4» {P: A → _} {Q: (Σ x: A, P x) → _} (p: x = y) (w: Σ u: P x, Q ⟨x, u⟩):
--   transport (fun (x: A) => Σ u: P x, Q ⟨x, u⟩) p w =
--     ⟨p₊ w.1, transport _ ((«2.7.2» _ _).2.1 ⟨p, refl⟩) w.2⟩
-- := sorry

#check LE
#check Nat.le_succ_of_le