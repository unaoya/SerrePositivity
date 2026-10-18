module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedTransportCoefficients

/-!
概要：元の係数図式から weighted nerve の strict transport 図式への自然な比較。
方針：各値を under 圏の構造射で輸送した族を weighted nerve に写し、相対 curry する。
規約：図式の Kan 性を仮定せずに自然変換を構成する。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の元の strict な係数図式の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：係数の値 H(i) は under 圏の nerve 上の weighted nerve の族を与える。
方針：底の射列に忘却関手を後合成し、輸送の係数を添える。
規約：元の weighted nerve の全空間に値を持つ。
使われ方：Kerodon 5.3.3.1、5.3.5.7 の strict transport の標準の族。 -/
noncomputable def weightedTransportFamily (H : I ⥤ SSet.{u}) (i : I) :
    nerve (Under i) ⊗ H.obj i ⟶ weightedNerve H where
  app d := ↾fun s => ⟨s.1 ⋙ Under.forget i,
    weightedTransportCoefficients H s.1 (SSet.yonedaEquiv.symm s.2)⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, a⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change weightedTransportCoefficients H ((SimplexCategory.toCat.map α.unop).toFunctor ⋙ σ)
      (SSet.yonedaEquiv.symm ((H.obj i).map α a)) =
        simplexPrefixWeightRestriction α.unop ≫ Functor.whiskerLeft
          (SimplexCategory.toCat.map α.unop).toFunctor
            (weightedTransportCoefficients H σ (SSet.yonedaEquiv.symm a))
    have hy : SSet.yonedaEquiv.symm ((H.obj i).map α a) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm a :=
      (SSet.yonedaEquiv_symm_naturality_left (X := H.obj i) α.unop a).symm
    rw [hy]
    exact weightedTransportCoefficients_restriction H α.unop σ _

/-- 概要：輸送の族は底で under 圏の忘却関手に一致する。
方針：各単体の底の射列を計算する。
規約：係数のパラメータは底では忘れる。
使われ方：Kerodon 5.3.1.5、5.3.5.7 の相対関手空間へ curry する条件。 -/
lemma weightedTransportFamily_projection (H : I ⥤ SSet.{u}) (i : I) :
    weightedTransportFamily H i ≫ weightedNerveProjection H =
      fst (nerve (Under i)) (H.obj i) ≫ nerveMap (Under.forget i) := rfl

/-- 概要：始点の射による under 圏の制限は元の係数値での輸送と一致する。
方針：各単体で輸送の係数の underMap の公式と Yoneda の後合成の式を使う。
規約：底を保つ実際の族の等式。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の元の図式から strict transport への自然性。 -/
lemma weightedTransportFamily_underMap (H : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
    (nerveUnderMap f ▷ H.obj i) ≫ weightedTransportFamily H i =
      (nerve (Under j) ◁ H.map f) ≫ weightedTransportFamily H j := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  change (⟨σ ⋙ Under.forget j,
    weightedTransportCoefficients H (σ ⋙ Under.map f) (SSet.yonedaEquiv.symm a)⟩ :
      weightedNerveSimplex H n) = ⟨σ ⋙ Under.forget j, weightedTransportCoefficients H σ
        (SSet.yonedaEquiv.symm ((H.map f).app (Opposite.op ⦋n⦌) a))⟩
  rw [weightedTransportCoefficients_underMap, SSet.yonedaEquiv_symm_comp]

/-- 概要：H(i) から weighted nerve の strict transport の i での値への標準射。
方針：under 圏全体への輸送の族を相対関手空間へ curry する。
規約：充填性や同値性はこの射の定義には要求しない。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の係数値の strict transport での回収。 -/
noncomputable def weightedTransportUnitComponent (H : I ⥤ SSet.{u}) (i : I) :
    H.obj i ⟶ leftStrictTransport (weightedNerveProjection H) i :=
  relativeFunctorCurry (p := weightedNerveProjection H) (a := nerveMap (Under.forget i))
    (weightedTransportFamily H i) (weightedTransportFamily_projection H i)

/-- 概要：標準射を相対関手として評価すると under 圏への輸送の族になる。
方針：相対 curry と uncurry の逆関係を使う。
規約：全空間への実際の族の等式。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の比較射の計算式。 -/
lemma weightedTransportUnitComponent_evaluation (H : I ⥤ SSet.{u}) (i : I) :
    relativeFunctorUncurry (weightedTransportUnitComponent H i) =
      weightedTransportFamily H i := relativeFunctorUncurry_curry _ _

/-- 概要：各係数値から strict transport への標準射は図式の射と可換である。
方針：相対評価の単射性で under 圏の制限と輸送の族の自然性へ戻す。
規約：図式全体の自然変換を作る厳密な等式。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の strict な係数図式の比較。 -/
lemma weightedTransportUnitComponent_naturality (H : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
    H.map f ≫ weightedTransportUnitComponent H j =
      weightedTransportUnitComponent H i ≫
        leftStrictTransportMap (weightedNerveProjection H) f := by
  apply relativeFunctorUncurry_injective (weightedNerveProjection H)
    (nerveMap (Under.forget j))
  change relativeFunctorUncurry (H.map f ≫ weightedTransportUnitComponent H j) =
    relativeFunctorUncurry (weightedTransportUnitComponent H i ≫ relativeFunctorPre
      (weightedNerveProjection H) (nerveMap (Under.forget i)) (nerveUnderMap f))
  rw [relativeFunctorUncurry_parameter, weightedTransportUnitComponent_evaluation,
    relativeFunctorUncurry_pre, weightedTransportUnitComponent_evaluation]
  exact (weightedTransportFamily_underMap H f).symm

/-- 概要：元の係数図式は weighted nerve の strict transport 図式へ自然に写る。
方針：全ての値の標準射と構造射に関する自然性を束ねる。
規約：任意の単体集合値図式について定義する。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の元の Hom 図式との自然な比較の模型。 -/
noncomputable def weightedTransportUnit (H : I ⥤ SSet.{u}) :
    H ⟶ leftStrictTransportDiagram (weightedNerveProjection H) where
  app := weightedTransportUnitComponent H
  naturality _ _ f := weightedTransportUnitComponent_naturality H f

end SerrePositivity.InfinityCategories.HomotopyLimits
