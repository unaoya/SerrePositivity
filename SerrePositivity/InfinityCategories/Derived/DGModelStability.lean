module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaRepresentableNerve
public import SerrePositivity.InfinityCategories.Derived.CellDGResolutionNerve
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability

/-! # dg nerve の表現可能模型と平坦模型の安定性の比較

概要：実際の ∞ 圏同値により安定性を比較し、両向きの関手の完全性を得る。
方針：表現可能 Yoneda と具体的 cell 分解の同値に一般の輸送定理を適用する。
規約：各 dg 圏自体の安定性はここでは仮定も結論も追加しない。
使われ方：β3 の前三角 dg 圏と平坦商の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の dg nerve の安定性と表現可能部分の nerve の安定性は同値。 -/
lemma dgYonedaRepresentableNerve_isStable_iff :
    IsStable (dgNerve A D) ↔ IsStable (dgNerve A (RepresentableDGCategory A D)) :=
  (dgYonedaRepresentableNerveEquivalence A D).isStable_iff

/-- 表現可能部分への実際の dg Yoneda の nerve は完全。 -/
lemma representableDGYonedaNerve_isExactFunctor :
    IsExactFunctor (dgNerve.map (representableDGYoneda A D)) :=
  isExactFunctor_of_isQCatEquivalence (dgYonedaRepresentableNerveEquivalence A D).isQCatEquivalence

/-- 平坦 cell 分解の nerve の安定性と元の nerve の安定性は同値。 -/
lemma dgCellResolutionNerve_isStable_iff :
    IsStable (dgNerve A (DGCategoryCellResolution.Source A D)) ↔ IsStable (dgNerve A D) :=
  (dgCellResolutionNerveEquivalence A D).isStable_iff

/-- 平坦 cell 分解の実際の増大関手の nerve は完全。 -/
lemma dgCellAugmentationNerve_isExactFunctor :
    IsExactFunctor (dgNerve.map (DGCategoryCellResolution.augmentation A D)) :=
  isExactFunctor_of_isQCatEquivalence (dgCellResolutionNerveEquivalence A D).isQCatEquivalence

/-- 平坦 cell 分解の nerve の選んだ逆関手も完全。 -/
lemma dgCellResolutionNerveInverse_isExactFunctor :
    IsExactFunctor (dgCellResolutionNerveEquivalence A D).inv :=
  isExactFunctor_of_isQCatEquivalence (dgCellResolutionNerveEquivalence A D).symm.isQCatEquivalence

end SerrePositivity.InfinityCategories
