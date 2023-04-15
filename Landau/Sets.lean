import Geometry.Logic

abbrev Set := Prop
def f (α β : Set) : Set := α → β
-- def g (α β : Set) : Set := α × β  
#check (Prop : Type)
#check (False : Set)
#check (And : Set → Set → Set)

namespace Set

axiom membership : Set → Set → Prop
@[default_instance] instance : Membership Set Set where mem := membership
def inclusion (A B : Set) := ∀ x, x ∈ A → x ∈ B
infix:50 " ⊆ " => inclusion

-- abbrev null := False

axiom extension : ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
axiom comprehension : ∀ φ : Set → Prop, ∀ z, ∃ y, ∀ x, x ∈ y → x ∈ z ∧ φ x
axiom pairing : ∀ x y, ∃ z, x ∈ z ∧ y ∈ z
axiom union : ∀ F, ∃ A, ∀ x, x ⊆ F → x ∈ A
axiom replacement (φ : Set → Set → Prop) (A : Set) :
  (∀ x, ∃! y, φ x y) → ∃ B, ∀ x, x ∈ A → ∃ y, y ∈ B ∧ φ x y

def int (v w y : Set) := ∀ x, x ∈ y ↔ x ∈ v ∧ x ∈ w

end Set

structure Witness {α : Sort u} (p : α → Prop) where
  w : α
  h : p w
def Witness.toProp (e : Witness p) : Prop := p e.w
instance : Coe (Witness p) Prop where coe := sorry

def extract {p : α → Prop} (h : (Witness p) ∧ q) : α :=
  h.left.w
#check Classical.choose