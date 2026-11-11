module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaRepresentableNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CellDGResolutionNerve
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability

/-! # dg nerve の表現可能模型と平坦模型の安定性の比較

概要：実際の ∞ 圏同値により安定性を比較し、両向きの関手の完全性を得る。
方針：表現可能 Yoneda と具体的 cell 分解の同値に一般の輸送定理を適用する。
規約：各 dg 圏自体の安定性はここでは仮定も結論も追加しない。
使われ方：β3 の前三角 dg 圏と平坦商の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の dg nerve の安定性と表現可能部分の nerve の安定性は同値。 -/
lemma dgYonedaRepresentableNerve_isStable_iff :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RepresentableDGCategory A D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaRepresentableNerveEquivalence A D).isStable_iff

/-- 表現可能部分への実際の dg Yoneda の nerve は完全。 -/
lemma representableDGYonedaNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.representableDGYoneda A D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaRepresentableNerveEquivalence A D).isQCatEquivalence

/-- 平坦 cell 分解の nerve の安定性と元の nerve の安定性は同値。 -/
lemma dgCellResolutionNerve_isStable_iff :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGCategoryCellResolution.Source A D)) ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D).isStable_iff

/-- 平坦 cell 分解の実際の増大関手の nerve は完全。 -/
lemma dgCellAugmentationNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D).isQCatEquivalence

/-- 平坦 cell 分解の nerve の選んだ逆関手も完全。 -/
lemma dgCellResolutionNerveInverse_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D).inv :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D).symm.isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
