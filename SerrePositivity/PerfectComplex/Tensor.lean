module
public import SerrePositivity.PerfectComplex.ClosedSupportRelations
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-! # Integer-indexed tensor products of cochain complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The standard total tensor complex, with the integer cochain sign convention. -/
abbrev cochainTensor (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.tensorObj P Q

/-- The inclusion of the summand of bidegree (i,j). -/
abbrev cochainTensorι (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    P.X i ⊗ Q.X j ⟶ (cochainTensor P Q).X (i + j) :=
  ιTensorObj P Q i j (i + j) rfl

/-- Tensoring two chain maps gives a chain map. -/
abbrev cochainTensorMap {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') : cochainTensor P Q ⟶ cochainTensor P' Q' :=
  HomologicalComplex.tensorHom f g

/-- The associative comparison for the chosen total tensor complex. -/
abbrev cochainTensorAssociator (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor P Q) T ≅ cochainTensor P (cochainTensor Q T) :=
  HomologicalComplex.associator P Q T

/-- The total tensor differential squares to zero. -/
lemma cochainTensor_d_comp_d (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j k : ℤ) :
    (cochainTensor P Q).d i j ≫ (cochainTensor P Q).d j k = 0 :=
  (cochainTensor P Q).d_comp_d i j k

/-- The differential on a homogeneous tensor has the standard Koszul sign. -/
lemma cochainTensorι_d (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    cochainTensorι P Q i j ≫ (cochainTensor P Q).d (i + j) (i + j + 1) =
      (P.d i (i + 1) ▷ Q.X j) ≫
        ιTensorObj P Q (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫
        ιTensorObj P Q i (j + 1) (i + j + 1) (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ rfl _ _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ rfl _ (by dsimp; omega)]
  simp

/-- Each degree is the coproduct over bidegrees with the prescribed sum. -/
abbrev cochainTensorSummand (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) : ModuleCat.{u} R := P.X ij.val.1 ⊗ Q.X ij.val.2

/-- The chosen totalization and its categorical coproduct model agree. -/
def cochainTensorXIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (cochainTensor P Q).X n ≅ ∐ (cochainTensorSummand P Q n) := Iso.refl _

/-- The degree-zero unit complex for the chosen tensor. -/
abbrev cochainTensorUnit : CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℤ)

/-- Left unit comparison. -/
abbrev cochainTensorLeftUnitor (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor cochainTensorUnit P ≅ P := HomologicalComplex.leftUnitor P

/-- Right unit comparison. -/
abbrev cochainTensorRightUnitor (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor P cochainTensorUnit ≅ P := HomologicalComplex.rightUnitor P
end SerrePositivity
