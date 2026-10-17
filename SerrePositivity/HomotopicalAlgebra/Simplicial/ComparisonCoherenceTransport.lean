module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanComparisonSquare
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport

/-! # Transport selected comparison tetrahedra and a whole comparison disc

Every selected cone face and the common diagonal are transported by the
same actual map of parameter mapping spaces. Restriction therefore
preserves the entire higher fillers, not just their boundary classes.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonCoherenceTransport
open KanComparisonTriangle
variable {T K T' K' : SSet.{v}}
  {f₀ f₁ f₂ f₃ z : T ⟶ K} {f₀' f₁' f₂' f₃' z' : T' ⟶ K'}
  (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
  (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)
  (F₀' : SSet.Homotopy f₀' z') (F₁' : SSet.Homotopy f₁' z')
  (F₂' : SSet.Homotopy f₂' z') (F₃' : SSet.Homotopy f₃' z')
  (q : (ihom T).obj K ⟶ (ihom T').obj K')
  (h₀ : curry F₀.h ≫ q = curry F₀'.h) (h₁ : curry F₁.h ≫ q = curry F₁'.h)
  (h₂ : curry F₂.h ≫ q = curry F₂'.h) (h₃ : curry F₃.h ≫ q = curry F₃'.h)

local notation "a'(" a ")" => ComparisonTriangleTransport.data F₀ F₁ F₀' F₁' q h₀ h₁ a
local notation "b'(" b ")" => ComparisonTriangleTransport.data F₀ F₂ F₀' F₂' q h₀ h₂ b
local notation "c'(" c ")" => ComparisonTriangleTransport.data F₁ F₂ F₁' F₂' q h₁ h₂ c

def tetrahedron (a : Data F₀ F₁) (b : Data F₀ F₂) (c : Data F₁ F₂)
    (d : KanComparisonTetrahedron.Filler F₀ F₁ F₂ a b c) :
    KanComparisonTetrahedron.Filler F₀' F₁' F₂' a'(a) b'(b) c'(c) where
  tetrahedron := d.tetrahedron ≫ q
  face_zero := by rw [← Category.assoc, d.face_zero]; rfl
  face_one := by rw [← Category.assoc, d.face_one]; rfl
  face_two := by rw [← Category.assoc, d.face_two]; rfl

lemma tetrahedron_triangle (a : Data F₀ F₁) (b : Data F₀ F₂) (c : Data F₁ F₂)
    (d : KanComparisonTetrahedron.Filler F₀ F₁ F₂ a b c) :
    KanComparisonTetrahedron.triangle F₀' F₁' F₂' a'(a) b'(b) c'(c)
        (tetrahedron F₀ F₁ F₂ F₀' F₁' F₂' q h₀ h₁ h₂ a b c d) =
      KanComparisonTetrahedron.triangle F₀ F₁ F₂ a b c d ≫ q :=
  (Category.assoc _ _ _).symm

variable (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)

local notation "ta" => ComparisonTriangleTransport.data F₀ F₁ F₀' F₁' q h₀ h₁ a
local notation "tb" => ComparisonTriangleTransport.data F₁ F₂ F₁' F₂' q h₁ h₂ b
local notation "tc" => ComparisonTriangleTransport.data F₀ F₃ F₀' F₃' q h₀ h₃ c
local notation "td" => ComparisonTriangleTransport.data F₃ F₂ F₃' F₂' q h₃ h₂ d

variable (e : KanComparisonSquare.Filler F₀ F₁ F₂ F₃ a b c d)

def square : KanComparisonSquare.Filler F₀' F₁' F₂' F₃' ta tb tc td where
  diagonal := ComparisonTriangleTransport.data F₀ F₂ F₀' F₂' q h₀ h₂ e.diagonal
  left := tetrahedron F₀ F₁ F₂ F₀' F₁' F₂' q h₀ h₁ h₂ a e.diagonal b e.left
  right := tetrahedron F₀ F₃ F₂ F₀' F₃' F₂' q h₀ h₃ h₂ c e.diagonal d e.right

lemma square_left_triangle :
    KanComparisonTetrahedron.triangle F₀' F₁' F₂' ta
      (square F₀ F₁ F₂ F₃ F₀' F₁' F₂' F₃' q h₀ h₁ h₂ h₃ a b c d e).diagonal tb
      (square F₀ F₁ F₂ F₃ F₀' F₁' F₂' F₃' q h₀ h₁ h₂ h₃ a b c d e).left =
    KanComparisonTetrahedron.triangle F₀ F₁ F₂ a e.diagonal b e.left ≫ q :=
  tetrahedron_triangle F₀ F₁ F₂ F₀' F₁' F₂' q h₀ h₁ h₂ a e.diagonal b e.left

lemma square_right_triangle :
    KanComparisonTetrahedron.triangle F₀' F₃' F₂' tc
      (square F₀ F₁ F₂ F₃ F₀' F₁' F₂' F₃' q h₀ h₁ h₂ h₃ a b c d e).diagonal td
      (square F₀ F₁ F₂ F₃ F₀' F₁' F₂' F₃' q h₀ h₁ h₂ h₃ a b c d e).right =
    KanComparisonTetrahedron.triangle F₀ F₃ F₂ c e.diagonal d e.right ≫ q :=
  tetrahedron_triangle F₀ F₃ F₂ F₀' F₃' F₂' q h₀ h₃ h₂ c e.diagonal d e.right

end SerrePositivity.SimplicialModel.ComparisonCoherenceTransport
