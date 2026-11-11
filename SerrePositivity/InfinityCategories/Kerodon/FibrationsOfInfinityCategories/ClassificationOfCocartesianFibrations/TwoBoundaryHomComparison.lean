module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryTargetPresentation

/-!
概要：実際の二次元標準境界の native Hom から、同じ分類先の区間 Hom への比較同値。
方針：両側の同じ pullback 表示で、構成済みの厳密 cospan 比較を戻す。
規約：元の境界と両補正比較の指定 path を保持する。
使われ方：高次境界と有限セルによる Hom 比較の降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryHomComparison
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftCoreFunctor p.val.hom q.val.hom
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramLiftOverFunctor
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)

local instance (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex ((N).obj (Opposite.op z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianNativeLiftCoreFunctor_obj_kan p.val.hom q.val.hom z
local instance (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex ((T).obj (Opposite.op z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalLiftOverFunctor_obj_kan p q z

/-- 元の実際の二次元境界上の全 native Hom を、同じ分類先 Hom へ写す比較。 -/
def cocartesianTwoBoundaryHomComparison :
    (N).obj (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 1 σ)) ⟶
      (T).obj (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 1 σ)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryNativePresentation.cocartesianTwoBoundaryNativePresentationIso p q).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryPullbackComparison j p q ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryTargetPresentation.cocartesianTwoBoundaryTargetPresentationIso p q).inv

/-- 構成した同じ実際の二次元境界比較自体は、追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryHomComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoBoundaryHomComparison j p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryNativePresentation.cocartesianTwoBoundaryNativePresentationIso p q)).isQCatEquivalence.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryPullbackComparison_isQCatEquivalence j p q).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryTargetPresentation.cocartesianTwoBoundaryTargetPresentationIso p q).symm).isQCatEquivalence)

/-- 同じ比較を分類先の pullback 表示へ戻すと、元の厳密 pullback 比較。 -/
lemma cocartesianTwoBoundaryHomComparison_presentation :
    cocartesianTwoBoundaryHomComparison j p q ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryTargetPresentation.cocartesianTwoBoundaryTargetPresentationIso p q).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryNativePresentation.cocartesianTwoBoundaryNativePresentationIso p q).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryPullbackComparison j p q := by
  simp only [cocartesianTwoBoundaryHomComparison, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryHomComparison
