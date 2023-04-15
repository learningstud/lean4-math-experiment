#check_failure Inv
class HInv (α: Sort u) (β: outParam (Sort v)) where hInv : α → β
postfix:arg "⁻¹" => HInv.hInv

#check Id
#check_failure Path
#check And
#check Eq

/-
abbrev Eq.ndrec.{u1, u2}
  {α : Sort u2} {a : α}
  {motive : α → Sort u1} (m : motive a)
  {b : α} (h : Eq a b)
: motive b := h.rec m
-/

abbrev _? := Prop

namespace HoTT1
inductive Path : α → α → _? where
  | refl (x : α) : Path x x

-- def D (α : Sort u) (x y : α) (p : Path α x y) := p
-- def ind (x y : )
-- axiom ind_principle.{u} :
--   ∀ D : (∀ α : Sort u, ∀ x y : α, ∀ p : Path α x y, Type),
--   ∀ d : (∀ a : α, D α a a (Path.refl a)), _
axiom ind.{u} {α}
  (D : ∀ x y : α, ∀ p : Path x y, Sort u)
  (d : ∀ a : α, D a a (Path.refl a))
  (x y : α) (p : Path x y)
: D x y p
axiom ind'.{u} {α}
  (D : ∀ x y : α, ∀ p : Path x y, Sort u)
  (d : ∀ a : α, D a a (Path.refl a))
  {x : α}
: ind D d x x (Path.refl x) = d x
example : Path x y → Path y x :=
  ind (fun x y p => Path y x) Path.refl x y
example : Path x y → Path y z → Path x z :=
  sorry
#check Coe
end HoTT1

namespace HoTT2
inductive Path : α → α → _? where
  | refl (x : α) : Path x x
#print Path.rec

theorem native_ind.{u} {α}
  {x : α}
  {D : (y : α) → Path x y → Sort u}
  (d : D x (Path.refl x))
  {y : α}
  (p : Path x y)
: D y p
:= Path.rec d p

theorem ind.{u} {α}
  (D : {x y : α} → Path x y → Sort u)
  (d : (x : α) → D (Path.refl x))
  {x y : α} (p : Path x y)
: D p
:= Path.rec (d x) p

axiom K.{u} {α} :
  ∀ {D : {x y : α} → Path x y → Sort u},
  ∀ {d : (x : α) → D (Path.refl x)},
  ∀ {x : α},
  ind D d (Path.refl x) = d x


example : Path x y → Path y x :=
  ind (@fun x y _ => Path y x) Path.refl
end HoTT2


namespace HoTT3
#check Eq
/--
Define equality in `Type` not `Prop`:
[Zulip thread](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Web.20Programming.20with.20Lean.204.html#222870854)

Using `α: Sort u` gives
```
invalid universe polymorphic type, the resultant universe is not Prop (i.e., 0), but it may be Prop for some parameter values (solution: use 'u+1' or 'max 1 u'
```
https://github.com/forked-from-1kasper/ground_zero/blob/a5aa24eceef3bb8330956a3bf93efb43b628f7cf/GroundZero/Cubical/Path.lean#L17
Compare the following. Why does the link above use the polymorphic `Type u`.
```lean4
inductive Path {α: Type u} (x: α): α → Type u
inductive Path (x: α): α → Type
```
-/
inductive Path (x: α): α → Type where
  /-- Similar to `Eq.rfl` not `Eq.refl` -/
  | refl: Path x x
/-
HoTT3.Path.rec.{u, v} :
  {α : Sort v} →
  {x : α} →
  {motive : (a : α) → Path x a → Sort u} →
  motive x Path.refl →
  {a : α} →
  (t : Path x a) →
  motive a t
-/
-- code generator does not support recursor 'HoTT3.Path.rec' yet, consider using
-- 'match ... with' and/or structural recursion
-- example (x y: α) (p: Path x y): Path y x :=
--   @Path.rec α x (fun (y: α) (p: Path x y) => Path y x)
--     Path.refl y p
example (x y: α) (p: Path x y): Path y x :=
  p.casesOn .refl -- match p with | .refl => .refl
example: Path x y → Path y x
  | .refl => .refl
  -- | _ => .refl -- BAD
example (p: Path x y): Path y x :=
  p.casesOn .refl
-- The above seems uncanny. A type can have more than those constructed by
-- constructors:
-- https://github.com/HoTT/book/issues/460#issuecomment-23393606
-- https://github.com/HoTT/book/issues/460#issuecomment-23446422
example: Path x y → Path y z → Path x z
  | .refl, .refl => .refl -- induction on both paths
example: Path x y → Path y z → Path x z
  | p, .refl => p -- induction on first path
  -- | p, _ => p -- BAD
example: Path x y → Path y z → Path x z
  | .refl, q => q -- induction on second path
  -- | _, q => q -- BAD
example (p: Path x y) (q: Path y z): Path x z :=
  q.casesOn (p.casesOn .refl)
example (p: Path x y) (q: Path y z): Path x z :=
  q.casesOn p
example (p: Path x y) (q: Path y z): Path x z :=
  p.casesOn (q.casesOn p)

/- ## Serious Stuff -/
namespace Path

/- https://github.com/forked-from-1kasper/ground_zero/blob/58ad68bb54e355f6c39beaee2b383879eccc9952/GroundZero/Types/Id.lean#L20 -/
@[inherit_doc] infix:50 (priority := high) " = "  => Path
def Refl (x: α) := @refl α x
-- **Theorem doesn't have computable code**
def symm: x = y → y = x
  | refl => refl
instance: HInv (x = y) (y = x) where hInv := symm

def trans: x = y → y = z → x = z
  | refl, refl => refl
instance: HMul (x = y) (y = z) (x = z) where hMul := trans

section 
variable {x y: α} (p: x = y)

/-- Cool. Changing `refl` to `rfl` gives a proof for `=` substituted with `=`. -/
def unitᵣ: p = (p * Refl y) :=
  p.casesOn refl -- Judgemental equality reduces `refl * Refl x` to `refl` on the RHS
def unitₗ: p = (Refl x * p) :=
  p.casesOn refl
example: p⁻¹⁻¹ = p :=
  p.casesOn refl
example: p * p⁻¹ = refl :=
  p.casesOn refl
example: p⁻¹ * p = refl :=
  p.casesOn refl
example (p: a = b) (q: b = c) (r: c = d): (p * q) * r = p * (q * r) :=
  r.casesOn (q.casesOn (p.casesOn refl))
end
#check_failure x

section

def wiskeringᵣ {p q: x = y} (a: p = q) (r: y = z): p * r = q * r :=
  r.casesOn <| (unitᵣ p)⁻¹ * a * (unitᵣ q)
infixl:70 " *ᵣ "   => wiskeringᵣ
def wiskeringₗ {r s: y = z} (q: y = x) (b: r = s): q⁻¹ * r = q⁻¹ * s :=
  q.casesOn <| (unitₗ r)⁻¹ * b * (unitₗ s)
infixl:70 " *ₗ "   => wiskeringₗ

abbrev Loop (x: α) := Path x x
abbrev Loop2 (x: α) := Loop (Refl x)
abbrev Refl2 (x: α) := Refl (Refl x)
example (a: Loop x): Refl x * a = a * Refl x :=
  (unitₗ a)⁻¹ * unitᵣ a
example (a: Loop x): a = Refl x * a * Refl x :=
  (unitₗ a) * unitᵣ (Refl x * a)
example (a: Loop2 x): Refl2 x * a = a * Refl2 x :=
  (unitₗ a)⁻¹ * unitᵣ a
example (a b: Loop2 x): a * b = (Refl2 x) * a * (Refl2 x) * (Refl2 x) * b * (Refl2 x) :=
  sorry
/--
Eckmann-Hilton

Agda proofs
- https://github.com/piyush-kurur/hott/blob/master/agda/hott/topology/loopspace/eckmann-hilton.agda
- https://github.com/dlicata335/hott-agda/blob/master/lib/HigherHomotopyAbelian.agda
-/
example (a b: Loop2 x): a * b = b * a :=
  sorry 
end

def ap {α: Sort u} (f: α → β) {x y: α} (p: x = y): f x = f y :=
  p.casesOn refl

#check CoeDep

end Path
end HoTT3