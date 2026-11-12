module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EmptyCocartesianHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningHomInterval
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexAttachmentOver

/-!
概要：実際の零単体の空境界で、native Hom と元の分類先 Hom の比較を閉じる。
方針：標準境界の始対象性を同じ空境界比較へ適用し、元の大域作用との厳密な可換式を得る。
規約：元の分類主写像・全相対 Hom と同じ制限を保持する。
使われ方：標準境界の次元による分類 Hom 比較の帰納の初段。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 実際の標準零単体の境界は始対象。 -/
def zeroSimplexBoundary_isInitial : IsInitial (boundary 0 : SSet.{u}) := by
  rw [boundary_zero]
  exact Subcomplex.isInitialBot

/-- 元の零単体の同じ空境界上の native Hom と分類先 Hom の厳密な比較同型。 -/
def cocartesianZeroBoundaryHomComparisonIso {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) (σ : (Δ[0] : SSet.{u}) ⟶ B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.emptyCocartesianHomComparisonIso p q P Q (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexAttachmentOver.boundary 0 σ)
    zeroSimplexBoundary_isInitial

/-- 同じ空境界の比較は、元の分類写像の全 Hom 作用と厳密に可換。 -/
lemma cocartesianZeroBoundaryHomComparison_original
    {C : Type u} [Category.{u} C]
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) (σ : (Δ[0] : SSet.{u}) ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexAttachmentOver.boundary 0 σ) ≫
      (cocartesianZeroBoundaryHomComparisonIso p.val.hom q.val.hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom) σ).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexAttachmentOver.boundary 0 σ).hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.emptyCocartesianHomComparison_factorization p.val.hom q.val.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexAttachmentOver.boundary 0 σ) zeroSimplexBoundary_isInitial _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
