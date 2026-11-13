module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinder
public import SerrePositivity.KST.SConstruction.BinaryCofanSourceIsos
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SmashMonomorphisms
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # 元の自由点つき区間の両端境界と smash の余積表示
概要：既存の同じ自由点つき境界を、同じ円柱の二つの端点へ移す。
方針：境界の実余積表示を右 smash し、同じ元の左単位同型で源を戻す。
規約：第一成分は時刻一、第二は時刻零。使われ方：写像円柱源比較の単射性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open Spectra
open scoped Simplicial

/-- 既存の同じ境界包含を、元の円柱区間の型で保持する。 -/
def pointedTensorBoundaryInclusion : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} ⟶ pointedTensorInterval.{u} :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u}

/-- 元の境界の終点を区間へ入れると、同じ時刻一の端点射。 -/
lemma pointedTensorBoundaryEnd_inclusion :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} ≫ pointedTensorBoundaryInclusion = pointedTensorIntervalEnd 1 := by
  change PointedObject.adjoinFunctor.map coprod.inl ≫
    PointedObject.adjoinFunctor.map
      (show (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) from _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right) =
      PointedObject.adjoinFunctor.map
        (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 1))
  erw [← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl]

/-- 元の境界の始点を区間へ入れると、同じ時刻零の端点射。 -/
lemma pointedTensorBoundaryStart_inclusion :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u} ≫ pointedTensorBoundaryInclusion = pointedTensorIntervalEnd 0 := by
  change PointedObject.adjoinFunctor.map coprod.inr ≫
    PointedObject.adjoinFunctor.map
      (show (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) from _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right) =
      PointedObject.adjoinFunctor.map
        (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 0))
  erw [← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr]

/-- 同じ元の境界の右 smash は、基礎単体集合上で単射。 -/
instance pointedTensorBoundaryTensor_mono (X : PointedSimplicialSet.{u}) :
    Mono (pointedTensorBoundaryInclusion.{u} ▷ X).right := by
  change Mono (PointedObject.smashMap pointedTensorBoundaryInclusion.{u} (𝟙 X)).right
  let _ : Mono pointedTensorBoundaryInclusion.{u}.right := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion_mono
  let g : X ⟶ X := 𝟙 X
  let _ : Mono g.right := by
    change Mono (𝟙 X.right)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_mono
    pointedTensorBoundaryInclusion.{u} g

/-- 同じ元の境界を smash したものは、二つの同じ X の実余積を表す。 -/
def pointedTensorBoundaryIsColimit (X : PointedSimplicialSet.{u}) :
    IsColimit (BinaryCofan.mk ((λ_ X).inv ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} ▷ X)
      ((λ_ X).inv ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u} ▷ X)) :=
  binaryCofanSourceIsos
    (mapIsColimitOfPreservesOfIsColimit (tensorRight X) _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryIsColimit) (λ_ X).symm (λ_ X).symm

end SerrePositivity.KST.SConstruction
