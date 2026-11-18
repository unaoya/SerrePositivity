module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.FreeHammockCoefficientLaws
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockEnriched
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveFunctor

/-!
# 元の自由 hammock の係数写像の全 coherent nerve

概要：Dwyer–Kan §9 の同じ左右比較の係数正方形を全 nerve へ移す。
方針：元の単位・合成則を束ね、同じ Ex∞ と coherent nerve を適用する。
規約：全 Hom 写像は既存の係数写像そのもの。
使われ方：HA §4.2.3 の同じ BE 加群族で指定局所化辺を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C D : RelativeCategory.{u}} (F : C ⟶ D)

/-- 概要：同じ自由 hammock の係数作用を全豊穣関手に束ねる（Dwyer–Kan §9）。
方針：元の Hom 写像の単位・合成則を使う。
規約：全語・全次数を保つ。使われ方：同じ Kan 化への入力。 -/
def freeHammockCoefficientEnriched :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects D) where
  obj X := F.functor.obj X
  map X Y := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y
  map_id X := freeHammockCoefficient_unit F X
  map_comp X Y Z := freeHammockCoefficient_comp F X Y Z

/-- 概要：同じ自由 hammock の係数作用の実 Kan 豊穣関手（Dwyer–Kan §9）。
方針：同じ Ex∞ の monoidal 移送を適用する。
規約：元の対象写像。使われ方：左右比較の全 nerve の自然性。 -/
def kanFreeHammockCoefficientFunctor :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory D) :=
  (show EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockObjects C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockObjects D) from
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exInfinityEnrichedFunctor.{u, u, u, u, u}
      (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects C) (D := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects D) (freeHammockCoefficientEnriched F))

/-- 概要：同じ自由 hammock の係数作用の全 nerve（HTT §1.1.5）。
方針：同じ Kan 豊穣関手の coherent nerve を取る。
規約：全単体を持つ実写像。使われ方：同じ源の係数比較。 -/
def kanFreeHammockCoefficientNerve : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockNerve C ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockNerve D :=
  coherentNerveMap (kanFreeHammockCoefficientFunctor F)

/-- 概要：同じ Kan 自由係数作用と augmentation の厳密な自然性（Dwyer–Kan §9）。
方針：元の Hom 正方形を同じ Ex∞ の関手性で移す。
規約：豊穣関手の等式。使われ方：元の hammock 側との比較。 -/
lemma kanFreeHammockCoefficient_augmentation :
    (kanFreeHammockCoefficientFunctor F).comp SSet (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationFunctor D) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationFunctor C).comp SSet (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F) := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro X Y
  change (exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y) ≫
    exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation D (F.functor.obj X) (F.functor.obj Y))) ≫ 𝟙 _ =
    exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y) ≫
      exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y)
  rw [Category.comp_id, ← exInfinity.map_comp, ← exInfinity.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap_augmentation]

/-- 概要：同じ Kan 自由係数作用と自由局所化比較の厳密な自然性（Dwyer–Kan §9）。
方針：元の Hom 正方形を同じ Ex∞ の関手性で移す。
規約：豊穣関手の等式。使われ方：既存の局所化 nerve との比較。 -/
lemma kanFreeHammockCoefficient_comparison :
    (kanFreeHammockCoefficientFunctor F).comp SSet (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonFunctor D) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonFunctor C).comp SSet (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationEnrichedMap F) := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro X Y
  change (exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y) ≫
    exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison D (F.functor.obj X) (F.functor.obj Y))) ≫ 𝟙 _ =
    exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y) ≫
      exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y)
  rw [Category.comp_id, ← exInfinity.map_comp, ← exInfinity.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap_comparison]

/-- 概要：同じ augmentation の係数自然性は全 nerve でも厳密（HTT §1.1.5）。
方針：豊穣関手の同じ等式を coherent nerve へ送る。
規約：全単体での等式。使われ方：指定局所化の源との比較。 -/
lemma kanFreeHammockCoefficientNerve_augmentation :
    kanFreeHammockCoefficientNerve F ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationNerve D =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockAugmentationNerve C ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve F := by
  exact congrArg (fun K : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory D) =>
    coherentNerveMap K) (kanFreeHammockCoefficient_augmentation F)

/-- 概要：同じ自由局所化比較の係数自然性は全 nerve でも厳密（HTT §1.1.5）。
方針：豊穣関手の同じ等式を coherent nerve へ送る。
規約：全単体での等式。使われ方：同じ局所化の係数比較の回収。 -/
lemma kanFreeHammockCoefficientNerve_comparison :
    kanFreeHammockCoefficientNerve F ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonNerve D =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockComparisonNerve C ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap F := by
  exact congrArg (fun K : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockCategory C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory D) =>
    coherentNerveMap K) (kanFreeHammockCoefficient_comparison F)

attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] freeHammockCoefficientEnriched
attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] kanFreeHammockCoefficientFunctor
attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] kanFreeHammockCoefficientNerve
attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] kanFreeHammockCoefficient_augmentation
attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] kanFreeHammockCoefficient_comparison
attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] kanFreeHammockCoefficientNerve_augmentation
attribute [cite HTT "1.1.5.5" (partial := component) "coherent nerve の定義に対する、この自由局所化模型の係数作用と比較射の自然性だけを構成する。一般の局所化の普遍性は含まない。"] kanFreeHammockCoefficientNerve_comparison

end SerrePositivity.EInfinity.Modules
