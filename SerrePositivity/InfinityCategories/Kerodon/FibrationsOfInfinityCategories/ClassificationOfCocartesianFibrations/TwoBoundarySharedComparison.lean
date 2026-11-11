module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornSharedRestrictions
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryDiagramComparison

/-!
概要：二次境界の共有部分と同じ一次元境界の Hom 比較の端点表示を揃える。
方針：元の底上の対象の厳密な一致を先に書き換える。
規約：比較写像を変更しない。
使われ方：二次境界の厳密な cospan 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ

/-- 共有部分は、欠けた面の同じ標準境界そのもの。 -/
lemma cocartesianTwoBoundarySharedOver_eq :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.shared 1 1 σ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 τ := rfl

/-- 同じ共有部分の反変 Hom 図式の表示に揃えた境界比較。 -/
def cocartesianTwoBoundarySharedComparison (j : Fin 2) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
      SSet.uliftFunctor.{u + 1, u}).obj (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.shared 1 1 σ))) ⟶
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverFunctor (nerve (ULift.{u} (Fin 3)))).op ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)).obj
      (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.shared 1 1 σ))) := by
  rw [cocartesianTwoBoundarySharedOver_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramComparison j τ p q

/-- 端点を揃えた同じ共有境界比較自身は同値。 -/
lemma cocartesianTwoBoundarySharedComparison_isQCatEquivalence (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoBoundarySharedComparison p q j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramComparison_isQCatEquivalence j τ p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
