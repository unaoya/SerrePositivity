module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AnodyneNativeHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiniteSimplexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.InnerAnodyne

/-!
概要：全辺を覆う inner anodyne 部分底上で、元の native Hom を実際の分類先の区間 Hom へ写す。
方針：同じ native 制限の選んだ逆を、有限単体上の元の分類作用と制限へ合成する。
規約：元の作用との関手同型を保持し、部分底の充填性は要求しない。
使われ方：境界を内ホーンと残りの面に分ける相対比較の内ホーン側。

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
variable (n : ℕ)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 1)))))
  (a : Over (nerve (ULift.{u} (Fin (n + 1)))))
  (ha : innerAnodyneExtensions a.hom)
  (he : Function.Surjective (a.hom.app (Opposite.op ⦋1⦌)))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom

local instance : InnerFibration (pullback.fst a.hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst a.hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 同じ native 制限の逆から作る、部分底上の実際の分類先 Hom への比較。 -/
def cocartesianAnodyneNativeHomComparison :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AnodyneNativeHomEquivalence.cocartesianAnodyneNativeLiftRestrictionEquivalence p.val.hom q.val.hom a ha he).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map a.hom) P Q

/-- 部分底の比較は、元の大域の同じ Hom 作用へ関手同型で戻る。 -/
def cocartesianAnodyneNativeHomComparison_originalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom a ≫
        cocartesianAnodyneNativeHomComparison n p q a ha he)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map a.hom) P Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AnodyneNativeHomEquivalence.cocartesianAnodyneNativeLiftRestrictionEquivalence p.val.hom q.val.hom a ha he).homInvIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map a.hom) P Q))
    (by simp only [cocartesianAnodyneNativeHomComparison, Category.assoc]; rfl)
    (Category.id_comp _)

/-- 分類先でも inner anodyne な同じ部分底では、この元の native 比較自身が同値。 -/
lemma cocartesianAnodyneNativeHomComparison_isQCatEquivalence
    :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianAnodyneNativeHomComparison n p q a ha he) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AnodyneNativeHomEquivalence.cocartesianAnodyneNativeLiftRestrictionEquivalence p.val.hom q.val.hom a ha he).symm.isQCatEquivalence.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval_finite_isQCatEquivalence n p q).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_isQCatEquivalence_of_innerAnodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.innerAnodyneExtensions_ulift_map a.hom ha) P Q))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
