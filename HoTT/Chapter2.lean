/-
# Chapter 2. Homotopy type theory

**Conventions**:
- Indent anonymous sections whereas named sections are not indented.
- `abbrev` vs `def`?

**References**:
- [ground_zero](https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/Types/Id.lean)

-/
-- import HoTT.Prelude
set_option autoImplicit false -- for clarity

section
  universe u
  variable {A: Type u}

  /--
  A.k.a, `Id{A}(x,y)`.
  What about `inductive Path {α: Type u} (x: α): α → Type u`
  -/
  inductive Path: (startPoint endPoint: A) → Type u
    | refl {x: A}: Path x x
  @[inherit_doc] infix:50 (priority := high) " = " => Path
  abbrev Path.Refl (x: A) := @Path.refl A x

  section
    universe v
    variable (D: (x y: A) → (p: x = y) → Type v)
    variable (d: (a: A) → D a a .refl)

    def Path.ind (x y: A) (p: x = y): D x y p :=
      p.casesOn (d x)
    theorem «2.0.1» (a: A): Path.ind D d a a .refl = d a :=
      .refl
  end

  #check_failure ind
  export Path (refl Refl) -- `refl` and `Refl` are used throughout the book
  #check (refl: {x: A} → Path x x)
  #check (Refl: (x: A) → Path x x)
end

/-
## 2.1 Types are higher groupoids
-/

section «Lemma 2.1.1»
  universe u
  variable {A: Type u} {x y: A}
  /-- Lemma 2.1.1 -/
  def Path.inverse: (x = y) → (y = x)
    | refl => refl
  @[inherit_doc] postfix:arg "⁻¹" => Path.inverse
  #reduce refl⁻¹ -- `refl`
  -- instance: HInv (x = y) (y = x) where
  --   hInv := Path.inverse
end «Lemma 2.1.1»

section «Lemma 2.1.2»
  universe u
  variable {A: Type u} {x y z: A}
  /-- Lemma 2.1.2 -/
  def Path.concatenation: (x = y) → (y = z) → (x = z)
    | refl, refl => refl
  @[inherit_doc] infixl:60 " ⬝ " => Path.concatenation
  #reduce refl ⬝ refl
  -- instance: HMul (x = y) (y = z) (x = z) where
  --   hMul := Path.concatenate

  /-- `calc` requires `Trans` to be implemented for `_` on the LHS to work -/
  instance: Trans (@Path A) Path Path where
    trans := Path.concatenation
end «Lemma 2.1.2»

section «Lemma 2.1.4»
  universe u
  variable {A: Type u} {x y z w: A}
  variable (p p': x = y) (op: y = x) (q: y = z) (r: z = w)

  /-- Lemma 2.1.4 (ⅰ) -/
  def Path.con_refl: p = p ⬝ Refl y :=
    p.casesOn refl
  /-- Lemma 2.1.4 (ⅰ) -/
  def Path.refl_con: p = Refl x ⬝ p :=
    p.casesOn refl
  /-- Lemma 2.1.4 (ⅱ) -/
  example: p⁻¹ ⬝ p = refl :=
    p.casesOn refl
  #reduce refl⁻¹ ⬝ refl -- `refl`
  /-- Lemma 2.1.4 (ⅱ) -/
  example: p ⬝ p⁻¹ = refl :=
    p.casesOn refl
  #reduce refl ⬝ refl⁻¹ -- `refl`
  /-- Lemma 2.1.4 (ⅲ) -/
  def Path.inv_inv: p⁻¹⁻¹ = p :=
    p.casesOn refl
  #reduce refl⁻¹⁻¹ -- `refl`
  /-- Lemma 2.1.4 (ⅳ) -/
  def Path.con_assoc: (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
    r.casesOn (q.casesOn (p.casesOn refl))
  #reduce (refl ⬝ refl) ⬝ refl -- `refl`
  #reduce refl ⬝ (refl ⬝ refl) -- `refl`

  /-! Extras -/
  /-- Bad name -/
  def Path.con_bridge: p ⬝ refl = refl ⬝ p :=
    p.casesOn refl
  def Path.con_inv: p ⬝ p⁻¹ = refl :=
    p.casesOn refl
  def Path.inv_con: p⁻¹ ⬝ p = refl :=
    p.casesOn refl
  def Path.con_cancel: p ⬝ q = p' ⬝ q → p = p' :=
    q.casesOn fun α => p.con_refl ⬝ α ⬝ p'.con_refl⁻¹
  example: (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
    q.casesOn (p.casesOn refl)
  example: p⁻¹ = op → p = op⁻¹ :=
    sorry
  example: p = op⁻¹ → p⁻¹ = op :=
    sorry
  
end «Lemma 2.1.4»

section «Theorem 2.1.6»
  universe u
  variable {A: Type u}

  /-- Right whiskering by induction on `r` -/
  def Path.right_whiskering {a b c: A} {p q: a = b} (α: p = q) (r: b = c):
    p ⬝ r = q ⬝ r
  := r.casesOn <| p.con_refl⁻¹ ⬝ α ⬝ q.con_refl
  -- := α.casesOn refl
  @[inherit_doc] infix:60 " ⬝ᵣ " => Path.right_whiskering
  /-- Left whiskering by induction on `r` -/
  theorem Path.left_whiskering {a b c: A} (q: a = b) {r s: b = c} (β: r = s):
    q ⬝ r = q ⬝ s
  -- := calc q ⬝ r
  --   = q⁻¹⁻¹ ⬝ r := q.inv_inv⁻¹ ⬝ᵣ r
  -- _ = q⁻¹⁻¹ ⬝ s := q⁻¹.casesOn (r.refl_con⁻¹ ⬝ β ⬝ s.refl_con)
  -- _ = q ⬝ s := q.inv_inv ⬝ᵣ s
  -- := by induction q with | refl => exact r.refl_con⁻¹ ⬝ β ⬝ s.refl_con
  := β.casesOn refl
  @[inherit_doc] infix:60 " ⬝ₗ " => Path.left_whiskering
  
  -- abbrev Loop (a: A) := Path a a
  -- abbrev Loop2 (a: A) := Loop (Refl a)

  -- variable {a: A} (α β: Loop2 a)
  -- def «Eckmann-Hilton»: α ⬝ β = β ⬝ α :=
  --   sorry
end «Theorem 2.1.6»

section «Definition 2.1.7»
  universe u
  #print Prod
  structure PointedType where
    carrier: Type u
    basepoint: carrier
  instance : CoeSort PointedType (Type u) where
    coe P := P.carrier
end «Definition 2.1.7»

section «Definition 2.1.8»
  abbrev LoopSpace (P: PointedType) :=
    let a := P.basepoint
    PointedType.mk (a = a) (Refl a)
  def Ω (n: Nat) (P: PointedType): PointedType :=
    match n with
    | 0 => P
    | .succ n => Ω n (LoopSpace P)
end «Definition 2.1.8»

/-!
section «Definition 2.1.7»
  universe u
  #print Prod
  structure PointedType (A: Type u) where
    basepoint: A
  instance {A: Type u}: CoeSort (PointedType A) (Type u) where
    coe _ := A
end «Definition 2.1.7»

section «Definition 2.1.8»
  abbrev LoopSpace.{u} {A: Type u} (P: PointedType A) :=
    PointedType.mk (Refl P.basepoint)
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

/-
## 2.2 Functions are functors
-/

section «Lemma 2.2.1»
  universe u v
  variable {A: Type u} {B: Type v} (f: A → B) {x y: A}
  def ap : x = y → f x = f y
    | refl => refl
  #reduce ap f (Refl x) -- `@refl B (f x) : f x = f x`
end «Lemma 2.2.1»

/-!
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
  universe u v w
  variable {A: Type u} {B: Type v} {C: Type w} (f: A → B) (g: B → C)
  variable {x y z: A} (p: x = y) (q: y = z)

  /-- Lemma 2.2.2 (ⅰ) -/
  example: ap f (p ⬝ q) = ap f p ⬝ ap f q :=
    q.casesOn (p.casesOn refl)
  /-- Lemma 2.2.2 (ⅱ) -/
  example: ap f p⁻¹ = (ap f p)⁻¹ :=
    p.casesOn refl
  /-- Lemma 2.2.2 (ⅲ) -/
  example: ap g (ap f p) = ap (g ∘ f) p := -- Book version
    p.casesOn refl
  example: (ap g ∘ ap f) p = ap (g ∘ f) p := -- My version
    p.casesOn refl
  /-- Lemma 2.2.2 (ⅳ) -/
  def Path.ap_id: ap id p = p :=
    p.casesOn refl
  
end «Lemma 2.2.2»

/-
## 2.3 Type families are fibrations
-/

section «Lemma 2.3.1»
  universe u v
  variable {A: Type u} {P: A → Type v} {x y: A}
  /-- Lemma 2.3.1; there is no unicode subscript `*`, so I use `+` instead. -/
  protected def Path.Transport: (x = y) → P x → P y
    | refl => id
  @[inherit_doc] postfix:max "₊" => Path.Transport
  abbrev Path.transport (P: A → Type v) := @Path.Transport A P x y
  export Path (transport) -- `transportᴾ(p,-): P(x) → P(y)` is used often.
end «Lemma 2.3.1»

section «Lemma 2.3.2»
  universe 𝒰 𝒱 -- 𝒲
  variable {A: Type 𝒰} {P: A → Type 𝒱} {x y: A}
  variable (u: P x) (p: x = y)
  /-- Lemma 2.3.2 -/
  def Path.lift: Sigma.mk x u = Sigma.mk y (p₊ u) :=
    p.casesOn refl
  export Path (lift)
  #reduce ap Sigma.fst (lift u refl) -- `@refl A x x`
  example: ap Sigma.fst (lift u p) = p :=
    p.casesOn refl
end «Lemma 2.3.2»

section «Lemma 2.3.4»
  universe u v
  variable {A: Type u} {P: A → Type v}
  /-- Lemma 2.3.4 -/
  def apd (f: (x: A) → P x) {x y: A} (p: x = y): p₊ (f x) = f y :=
    p.casesOn refl
  #print ap
end «Lemma 2.3.4»

section «Lemma 2.3.5»
  universe u v
  variable {A: Type u} {x y: A}
  /-- Lemma 2.3.5 -/
  def transportconst (B: Type v) (p: x = y) (b: B):
    transport (fun _ => B) p b = b
  :=
    p.casesOn refl
end «Lemma 2.3.5»

section «Lemma 2.3.8»
  universe u v
  variable {A: Type u} {B: Type v} (f: A → B) {x y: A} (p: x = y)
  def «Lemma 2.3.8»: apd f p = transportconst B p (f x) ⬝ ap f p :=
    p.casesOn refl
end «Lemma 2.3.8»

section
  -- set_option autoImplicit true
  variable {A: Type _} {B: Type _} {x y z: A}
  section
    variable (P: A → Type _) (p: x = y) (q: y = z) (u: P x)
    def «Lemma 2.3.9»: q₊ (p₊ u) = (p ⬝ q)₊ u :=
      q.casesOn (p.casesOn refl)
  end
  section
    variable (f: A → B) (P: B → Type _) (p: x = y) (u: P (f x))
    def «Lemma 2.3.10»: transport (P ∘ f) p u = transport P (ap f p) u :=
      p.casesOn refl
  end
  section
    variable (P Q: A → Type _) (f: ∀ x: A, P x → Q x) (p: x = y) (u: P x)
    def «Lemma 2.3.11»: transport Q p (f x u) = f y (transport P p u) :=
      p.casesOn refl
  end
end

/-
## 2.4 Homotopies and equivalences
-/
-- set_option autoImplicit true
variable {A: Type _} {B: Type _} {C: Type _} {P: A → Type _}

section «Definition 2.4.1»
  /-- Definition 2.4.1 (Homotopy). `abbrev` or `def`? -/
  abbrev homotopy (f g: (x: A) → P x) := (x: A) → f x = g x
  /- Is 50 the appropriate precedence? -/
  @[inherit_doc] infix:50 " ~ " => homotopy
end «Definition 2.4.1»

section «Lemma 2.4.2»
  example (f: (x: A) → P x): f ~ f
    | _ => refl
  example (f g: (x: A) → P x): f ~ g → g ~ f
    | p, x => (p x)⁻¹ -- (p x).casesOn refl
  example (f g h: (x: A) → P x): f ~ g → g ~ h → f ~ h
    | p, q, x => p x ⬝ q x -- (q x).casesOn ((p x).casesOn refl)
end «Lemma 2.4.2»

/-- Why doesn't `p.casesOn refl` make a proof? -/
def «Lemma 2.4.3» {f g: A → B} (H: f ~ g) {x y: A} (p: x = y):
  H x ⬝ ap g p = ap f p ⬝ H y
:=  p.casesOn (H x).con_bridge

def «Corollary 2.4.4» {f: A → A} (H: f ~ id) (x: A): H (f x) = ap f (H x) :=
  Path.con_cancel _ _ _ <| calc H (f x) ⬝ H x
                              = H (f x) ⬝ ap id (H x) := _ ⬝ₗ (Path.ap_id _)⁻¹
                            _ = ap f (H x) ⬝ H x      := «Lemma 2.4.3» H (H x)
--   calc H (f x)
--      = H (f x) ⬝ refl := Path.con_refl _
--    _ = H (f x) ⬝ (H x ⬝ (H x)⁻¹) := _ ⬝ₗ (Path.con_inv _)⁻¹
--    _ = H (f x) ⬝ H x ⬝ (H x)⁻¹ := (Path.con_assoc _ _ _)⁻¹
--    _ = ap f (H x) ⬝ H x ⬝ (H x)⁻¹ := naturality ⬝ᵣ _
--    _ = ap f (H x) ⬝ (H x ⬝ (H x)⁻¹) := Path.con_assoc _ _ _
--    _ = ap f (H x) ⬝ refl := _ ⬝ₗ Path.con_inv _
--    _ = ap f (H x) := (Path.con_refl _)⁻¹
-- where naturality: H (f x) ⬝ H x = ap f (H x) ⬝ H x :=
--   calc _ = H (f x) ⬝ ap id (H x) := _ ⬝ₗ (Path.ap_id _)⁻¹
--        _ = _ := «Lemma 2.4.3» H (H x)

section «Definition 2.4.6»
  structure QuasiInverse (f: A → B) where
    g: B → A
    α: f ∘ g ~ id
    β: g ∘ f ~ id
  def qinv (f: A → B) := Σ g: B → A, (f ∘ g ~ id) × (g ∘ f ~ id)
end «Definition 2.4.6»

section «Example 2.4.7»
  def qinv.refl: qinv (@id A) := ⟨id, Refl, Refl⟩
  #check (⟨id, Refl, Refl⟩: qinv id)
end «Example 2.4.7»

section «Example 2.4.8»
  variable {x y z: A} (p: x = y)
  example: qinv ((p ⬝ ·): (y = z) → (x = z)) :=
    ⟨(p⁻¹ ⬝ ·)
    , fun (q: x = z) => calc p ⬝ (p⁻¹ ⬝ q)
                           = (p ⬝ p⁻¹) ⬝ q := (Path.con_assoc _ _ _)⁻¹
                         _ = refl ⬝ q := Path.con_inv p ⬝ᵣ q
                         _ = q := (Path.refl_con _)⁻¹
    , fun (q: y = z) => calc p⁻¹ ⬝ (p ⬝ q)
                           = (p⁻¹ ⬝ p) ⬝ q := (Path.con_assoc _ _ _)⁻¹
                         _ = refl ⬝ q := Path.inv_con p ⬝ᵣ q
                         _ = q := (Path.refl_con _)⁻¹
    ⟩
  example: qinv ((p ⬝ ·): (y = z) → (x = z)) :=
    ⟨(p⁻¹ ⬝ ·), fun | refl => p.casesOn refl, fun | refl => p.casesOn refl⟩
  example: qinv ((p ⬝ ·): (y = z) → (x = z)) :=
    ⟨(p⁻¹ ⬝ ·), p.casesOn fun | refl => refl, p.casesOn fun | refl => refl⟩
  example: qinv ((· ⬝ p): (z = x) → (z = y)) :=
    ⟨(· ⬝ p⁻¹), p.casesOn fun | refl => refl, p.casesOn fun | refl => refl⟩
end «Example 2.4.8»

section «Example 2.4.9»
  variable {x y: A} (p: x = y) (P: A → Type _)
  example: qinv ((transport P p ·): P x → P y) :=
    ⟨(transport P p⁻¹ ·), p.casesOn Refl, p.casesOn Refl⟩
end «Example 2.4.9»

section «Definition 2.4.10»
  def isequiv (f: A → B) := (Σ g: B → A, f ∘ g ~ id) × (Σ h: B → A, h ∘ f ~ id)
  def qinv_is_isequiv (f: A → B): qinv f → isequiv f
    | ⟨g, α, β⟩ => ⟨⟨g, α⟩, g, β⟩
  def isequiv_is_qinv (f: A → B): isequiv f → qinv f
    | ⟨⟨g, α⟩, h, β⟩ =>
        let γ (x: B) := (β (g x))⁻¹ ⬝ ap h (α x)
        ⟨g, α, fun x => γ (f x) ⬝ β x⟩
  example (f: A → B) (e₁ e₂: isequiv f): e₁ = e₂ :=
    sorry
end «Definition 2.4.10»

section «Definition 2.4.11»
  /-- Type equivalence -/
  def equiv (A: Type _) (B: Type _) := (f: A → B) × isequiv f
  @[inherit_doc] infix:50 " ≃ " => equiv
end «Definition 2.4.11»

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
    | ⟨f, e⟩ => let ⟨g, p, q⟩: qinv f := e ; let m: qinv g := ⟨f, q, p⟩ ; m
      -- qinv_is_equiv ⟨f, q, p⟩
  /-- Lemma 2.4.12 (ⅲ) -/
  example: A ≃ B → B ≃ C → A ≃ C
    | ⟨f₁, e₁⟩, ⟨f₂, e₂⟩ =>
        let ⟨g₁, p₁, q₁⟩: qinv f₁ := e₁
        let ⟨g₂, p₂, q₂⟩: qinv f₂ := e₂
        let m: qinv (f₂ ∘ f₁) :=
        ⟨g₁ ∘ g₂
        , fun x => _
        , fun x => _
        ⟩
        m
end «Lemma 2.4.12»

/-
## 2.5 The higher groupoid structure of type formers
-/

/- 2.5.1 -/
-- example (b b': B) (c c': C): (Sigma.mk b c = Sigma.mk b' c') ≃ (b = b' × c = c') :=
--   sorry

/-
## 2.6 Cartesian product types
-/

section «Theorem 2.6.2»
end «Theorem 2.6.2»

abbrev Loop (a: A) := Path a a
abbrev Loop2 (a: A) := Loop (Refl a)

variable {a b c: A}
section
  variable {p q: a = b} {r s: b = c} (α: p = q) (β: r = s)
  def horizontalComposition := (α ⬝ᵣ r) ⬝ (q ⬝ₗ β)
  infix:60 " ★ " => horizontalComposition
  def horizontalComposition' := (p ⬝ₗ β) ⬝ (α ⬝ᵣ s)
  infix:60 " ★' " => horizontalComposition'
  def comp_unique: α ★ β = α ★' β :=
    sorry
    -- α.casesOn (β.casesOn refl)
end

variable (α β: Loop2 a)
example: α ⬝ᵣ refl = α :=
  calc α ⬝ᵣ refl
    = refl ⬝ α ⬝ refl := refl
  _ = α ⬝ refl := α.refl_con⁻¹ ⬝ᵣ refl
  _ = α := α.con_refl⁻¹
example: refl ⬝ₗ β = refl ⬝ β ⬝ refl :=
  sorry
  -- refl ⬝ β ⬝ refl := refl
def loop: α ★ β = α ⬝ β :=
  calc (α ⬝ᵣ refl) ⬝ (refl ⬝ₗ β)
     = refl ⬝ α ⬝ refl ⬝ (refl ⬝ₗ β) := refl
   _ = α ⬝ refl ⬝ (refl ⬝ₗ β) := (α.refl_con⁻¹ ⬝ᵣ refl) ⬝ᵣ _
   _ = α ⬝ (refl ⬝ₗ β) := α.con_refl⁻¹ ⬝ᵣ _
  --  _ = refl.con_refl⁻¹ ⬝ α ⬝ refl.con_refl ⬝ (refl.con_refl⁻¹ ⬝ β ⬝ refl.con_refl) := _ ⬝ᵣ refl
   _ = _ := sorry
def loop': α ★' β = β ⬝ α :=
  sorry
  -- calc (refl ⬝ₗ β) ⬝ (α ⬝ᵣ refl)
  --    = _ ⬝ _ := sorry
  --  _ = _ := sorry
def «Eckmann-Hilton»: α ⬝ β = β ⬝ α :=
  (loop α β)⁻¹ ⬝ comp_unique α β ⬝ loop' α β
  -- calc α ⬝ β
  --    = α ★ β := loop⁻¹
  --  _ = α ★' β := comp_unique
  --  _ = β ⬝ α := loop'
