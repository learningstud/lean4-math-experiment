import Geometry.Logic
import Geometry.Algebra

section sec_6_1

variable [Membership Point Line]

class IncidenceGeometry where
  I1 (A B : Point) : A ≠ B → ∃! l : Line, A ∈ l ∧ B ∈ l
  I2 (l : Line) : ∃ A B : Point, A ≠ B ∧ A ∈ l ∧ B ∈ l
  I3 : ∃ P : Point, ∃ l : Line, P ∉ l

theorem prop_6_1 (l m : Line) : l ≠ m → ∃? P : Point, P ∈ l ∧ P ∈ m := sorry

example : (1:ℚ) + (2:ℚ) = 3 := rfl

-- def Parallel (l m : Line) := ¬∃ P : Point, P ∈ l ∧ P ∈ m
-- infix:50 " ∥ " => Parallel 

-- axiom Playfair (A : Point) (l : Line) : ∃? m : Line, A ∈ m ∧ m ∥ l

end sec_6_1

-- Independence of I1, I2, I3, Playfair
section Independence

namespace G

variable [Membership Point Line]

def I1 := ∀ A B : Point, A ≠ B → ∃! l : Line, A ∈ l ∧ B ∈ l
def I2 := ∀ l : Line, ∃ A B : Point, A ≠ B ∧ A ∈ l ∧ B ∈ l
def I3 := ∃ P : Point, ∃ l : Line, P ∉ l

def Parallel (l m : Line) := ¬∃ P : Point, P ∈ l ∧ P ∈ m
infix:50 " ∥ " => Parallel

def P := ∀ A : Point, ∀ l : Line, ∃? m : Line, A ∈ m ∧ m ∥ l

end G

#check (⟨1, rfl⟩ : {x : Nat // x = 1})
#check Decidable

theorem fin1_zero (y : Fin 1) : y = 0 :=
  Fin.eq_of_val_eq (lt_one_eq_zero y.isLt)
where lt_one_eq_zero {n : Nat} (h : n < 1) : n = 0 :=
  match n with
  | 0 => rfl
  | Nat.succ m => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero m)

section I3

instance i : Membership (Fin 2) (Fin 1) where
  mem := fun _ _ => True
example : (0 : Fin 2) ∈ (1 : Fin 1) := trivial

example : G.I1 (Point := Fin 2) (Line := Fin 1) :=
  fun _ _ _ => ⟨_, ⟨⟨trivial, trivial⟩, fun y _ => fin1_zero y⟩⟩
example : G.I2 (Point := Fin 2) (Line := Fin 1) :=
  fun _ => ⟨0, 1, by decide, trivial, trivial⟩
example : ¬G.I3 (Point := Fin 2) (Line := Fin 1) :=
  fun h => absurd h (not_exists_not fun _ _ => trivial)

end I3

end Independence




namespace GG

def exactlyOneOf (p q r : Prop) := (p ∧ ¬q ∧ ¬r) ∨ (¬p ∧ q ∧ ¬r) ∨ (¬p ∧ ¬q ∧ r)

section

variable (A B C : Point)
def distinct := A ≠ B ∧ B ≠ C ∧ C ≠ A

variable [Membership Point Line]
def colinear := ∃ l : Line, A ∈ l ∧ B ∈ l ∧ C ∈ l
def Parallel (l m : Line) := ¬∃ P : Point, P ∈ l ∧ P ∈ m
infix:50 " // " => Parallel

end

class Betweeness (Point : Type u) where
  between (A B C : Point) : Prop
macro:max a:ident "#" b:ident "#" c:ident : term => `(Betweeness.between $a $b $c)
example [Betweeness Point] (A B C : Point) : A#B#C = Betweeness.between A B C := rfl

variable {Point : Type u} {Line : Type v}
variable [Membership Point Line]

def I1 := ∀ A B : Point, A ≠ B → ∃! l : Line, A ∈ l ∧ B ∈ l
def I2 := ∀ l : Line, ∃ A B : Point, A ≠ B ∧ A ∈ l ∧ B ∈ l
def I3 := ∃ P : Point, ∃ l : Line, P ∉ l

class IG (Point Line) [Membership Point Line] where
  one : I1 (Point := Point) (Line := Line)

def P := ∀ A : Point, ∀ l : Line, ∃? m : Line, A ∈ m ∧ m // l

variable [Betweeness Point]

def B1 := ∀ A B C : Point, A#B#C →
  distinct A B C ∧
  (∃ l : Line, A ∈ l ∧ B ∈ l ∧ C ∈ l) ∧ -- colinear
  C#B#A
def B2 := ∀ A B : Point, A ≠ B → ∃ C : Point, A#B#C
def B3 := ∀ A B C : Point, distinct A B C → exactlyOneOf A#B#C B#C#A C#A#B
  -- (A#B#C ∧ ¬B#C#A ∧ ¬C#A#B) ∨
  -- (¬A#B#C ∧ B#C#A ∧ ¬C#A#B) ∨
  -- (¬A#B#C ∧ ¬B#C#A ∧ C#A#B)

def Join [g : IG Point Line] {A B : Point} (h : A ≠ B) := g.one A B h
structure Line2 where
  A : Point
  B : Point
  distinct : A ≠ B
#check Exists.intro
noncomputable def Line2.toLine (l : @Line2 Point) (i : I1 (Point := Point) (Line := Line)) :=
  -- @I1 Point Line
  (Classical.inhabited_of_exists (i l.A l.B l.distinct)).default


structure Segment {Point} where
  A : Point
  B : Point
  distinct : A ≠ B
def Segment.eq {Point} := ∀ {x y : @Segment Point},
  x = y ↔ (x.A = y.A ∧ x.B = y.B) ∨ (x.A = y.B ∧ x.B = y.A)

inductive Plane where
  | ruler : Segment → Plane
  | compass : Segment → Plane

def Segment.congr {Point} (x y : @Segment Point) :=
  (x.A = y.A ∧ x.B = y.B) ∨ (x.A = y.B ∧ x.B = y.A)
instance {Point} : Equivalence (@Segment.congr Point) where
  refl := fun _ => Or.inl ⟨rfl, rfl⟩
  symm := fun hxy => hxy.elim
    (fun ⟨lhs, rhs⟩ => Or.inl ⟨lhs.symm, rhs.symm⟩)
    (fun ⟨lhs, rhs⟩ => Or.inr ⟨rhs.symm, lhs.symm⟩)
  trans := fun hxy hyz => hxy.elim
    (fun ⟨xAyA, xAyB⟩ => hyz.elim
      (fun ⟨yAzA, yBzB⟩ => Or.inl ⟨xAyA ▸ yAzA, xAyB ▸ yBzB⟩)
      (fun ⟨yAzB, yBzA⟩ => Or.inr ⟨xAyA ▸ yAzB, xAyB ▸ yBzA⟩)
    )
    (fun ⟨xAyB, xByA⟩ => hyz.elim
      (fun ⟨yAzA, yBzB⟩ => Or.inr ⟨xAyB ▸ yBzB, xByA ▸ yAzA⟩)
      (fun ⟨yAzB, yBzA⟩ => Or.inl ⟨xAyB ▸ yBzA, xByA ▸ yAzB⟩)
    )

class Congruence (α : Type u) where
  congr : α → α → Prop
  refl  : ∀ x, congr x x
  symm  : ∀ {x y}, congr x y → congr y x
  trans : ∀ {x y z}, congr x y → congr y z → congr x z
infix:50 " ~ " => Congruence.congr

-- example (A B : Point) (h : A ≠ B) :
--   ({O := A, P := B, distinct := h} : Ray) ~ ({O := A, P := B, distinct := h} : Ray)
-- := rfl

structure Ray where
  O : Point
  P : Point
  distinct : O ≠ P

structure Angle [inst : Membership Point Line] where
  O : Point
  P : Point
  Q : Point
  distinct : O ≠ P ∧ O ≠ Q
  noncolinear : ¬@colinear Point Line O P Q inst
def Angle.rayP [inst : Membership Point Line] (θ : @Angle Point Line inst) : @Ray Point :=
 { O := θ.O, P := θ.P, distinct := θ.distinct.left}
def Angle.rayQ [inst : Membership Point Line] (θ : @Angle Point Line inst) : @Ray Point :=
 { O := θ.O, P := θ.Q, distinct := θ.distinct.right}

-- def B4 := ∀ (A B C : Point), ¬colinear (Point := Point) (Line := Line) A B C →
--   ∀ l : Line, 

/-
Bl. If B is between A and C, (written A#B#C), then A,B,C are three distinct points on a line, and also C *B *A.
B2. For any two distinct points A, B, there exists a point C such that A#B#C.
B3. Given three distinct points on a line, one and only one of them is between
the other two.
-/

end GG