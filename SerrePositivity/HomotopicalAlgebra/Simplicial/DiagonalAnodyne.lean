module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # The actual diagonal preserves Reedy anodyne maps without a value model structure -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.BisimplicialModel

lemma relativeMatching_horn_rlp {E B : SSet.{v}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (n : ℕ) :
    SSet.modelCategoryQuillen.J.rlp
      (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
        (internalHomRight.map p)) := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have : Fibration (boundaryPullbackHom p n).π := SSet.fibration_pullbackObjObjπ _
  have h := (SSet.modelCategoryQuillen.fibration_iff (boundaryPullbackHom p n).π).mp this
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_iso_iff (relativeMatchingArrowIso p n)).mpr h

lemma diagonal_map_anodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp SSet.anodyneExtensions f) :
    SSet.anodyneExtensions (diagonal.map f) := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E T p hp
  have : ∀ j : SimplexCategoryᵒᵖ,
      HasLiftingProperty (relativeLatchingMap simplexOp j f)
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
    intro j
    have hr : SSet.modelCategoryQuillen.J.rlp
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
      induction j using Opposite.rec with | _ j =>
        induction j using SimplexCategory.rec with | _ n =>
          exact relativeMatching_horn_rlp p hp n
    exact (hf j) _ hr
  have h : HasLiftingProperty f (internalHomRight.map p) := Lifting.hasLiftingProperty simplexOp
  exact (Adjunction.hasLiftingProperty_iff diagonalInternalHomAdjunction f p).mpr h

lemma localized_diagonal_map_of_reedy_anodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp SSet.anodyneExtensions f) :
    IsIso (SimplicialModel.AnodyneHomotopy.anodyneQ.map (diagonal.map f)) :=
  Localization.inverts SimplicialModel.AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (diagonal_map_anodyne f hf)

end SerrePositivity.BisimplicialModel
