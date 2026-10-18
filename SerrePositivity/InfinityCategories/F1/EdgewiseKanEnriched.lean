module

public import SerrePositivity.InfinityCategories.F1.EdgewiseEnrichedComparison
public import SerrePositivity.InfinityCategories.F1.KanPointHomNaturality

/-!
概要：edgewise な Hom の解像をパラメーターとする Kan 複体の edgewise 解像の豊穣作用。
方針：対象と Hom の重みからの射を対にし、内部 Hom の評価を後合成する。
規約：高次の Hom のパラメーターも edgewise 解像する。
使われ方：Kerodon §8.1.1、Corollary 5.6.0.6、左右の Hom を自然に比較する共通の対象の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：edgewise 解像した対象と内部 Hom を共通の重みで評価する。
方針：二つの重みからの射の対を内部 Hom の評価へ送る。
規約：対象 X と Y は任意の単体集合。
使われ方：Kerodon §8.1.1、edgewise な豊穣作用の uncurry。 -/
def edgewiseInternalHomEvaluation (X Y : SSet.{u}) :
    edgewiseSubdivision X ⊗ edgewiseSubdivision ((ihom X).obj Y) ⟶ edgewiseSubdivision Y where
  app _ := ↾fun ⟨x, f⟩ ↦ lift x f ≫ (ihom.ev X).app Y
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f⟩
    change lift (edgewiseWeight.map α.unop ≫ x) (edgewiseWeight.map α.unop ≫ f) ≫
      (ihom.ev X).app Y = edgewiseWeight.map α.unop ≫ (lift x f ≫ (ihom.ev X).app Y)
    rw [← Category.assoc, comp_lift]

/-- 概要：edgewise な内部 Hom のパラメーターは解像した対象間の内部 Hom に作用する。
方針：共通の重みでの評価を curry する。
規約：元の Hom からの豊穣作用を無理に仮定せず、その edgewise 解像を始域とする。
使われ方：Kerodon §8.1.1、左右の係数比較を全ての高次の Hom で両立させる作用。 -/
def edgewiseKanEnrichedMap (X Y : SSet.{u}) :
    edgewiseSubdivision ((ihom X).obj Y) ⟶ (ihom (edgewiseSubdivision X)).obj (edgewiseSubdivision Y) :=
  curry (edgewiseInternalHomEvaluation X Y)

/-- 概要：対象の edgewise 解像は Hom を解像した圏から Kan 複体への豊穣関手。
方針：評価を重みの各単体で計算し、内部 Hom の単位・合成の式を使う。
規約：始域は EdgewiseEnrichedObject KanObject。
使われ方：Kerodon Corollary 5.6.0.6、元の対象と反転した対象を比較する共通の coherent な族。 -/
def edgewiseKanEnriched : EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject KanObject.{u}) KanObject.{u} where
  obj X := kanEdgewiseFunctor.obj X.val
  map X Y := edgewiseKanEnrichedMap X.val.obj Y.val.obj
  map_id X := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp X Y Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 概要：共通の重みの評価は右端射影と可換。
方針：右半分に制限した同じ二つの射を内部 Hom の評価へ入れる。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon §8.1.1、対象の edgewise 解像と元の対象の豊穣的な自然な比較。 -/
lemma edgewiseInternalHomEvaluation_right (X Y : SSet.{u}) :
    edgewiseInternalHomEvaluation X Y ≫ edgewiseRight Y =
      (edgewiseRight X ⊗ₘ edgewiseRight ((ihom X).obj Y)) ≫ (ihom.ev X).app Y := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  rfl

end SerrePositivity.InfinityCategories
