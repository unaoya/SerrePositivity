module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaReflectorDensity

/-!
概要：専用反映候補の単位と余単位を密度の大域的な普遍性で構成する。
方針：Yoneda 制限の全単射で同じ可逆 Kan 単位とその逆を延長する。
規約：関手圏の射として構成し、各点の射の独立な選択にしない。
使われ方：指定候補と包含の三角恒等式の証明。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]
    {L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C}
    (β : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ L))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) L β)

/-- 概要：包含後の同じ Kan 単位を全前層 Yoneda 上の単位候補として読む。
方針：指定包含後の全射の等式で両端を輸送する。
規約：元の可逆単位の h Fun の類を保持する。
使われ方：全前層圏上の単位の密度による延長。 -/
def sigmaReflectorYonedaUnit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ 𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
    (U := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)
    (V := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)
    (by rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion])
    (by rw [Category.assoc])
    ((hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)))

/-- 概要：同じ Kan 単位を P_Σ 上の制限の Yoneda 単位として読む。
方針：Yoneda の包含による因子化を延長先に合成する。
規約：元の単位と同じ全自然変換を保持する。
使われ方：余単位の密度による延長。 -/
def sigmaReflectorRestrictionYonedaUnit :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C ≫ L)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion])
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))

include hβ in
/-- 概要：P_Σ 制限上の同じ Yoneda 単位は可逆。
方針：元の単位の可逆性を端点の輸送で保つ。
規約：元の h Fun の射を判定する。
使われ方：逆単位から余単位を構成する。 -/
lemma sigmaReflectorRestrictionYonedaUnit_isIso :
    IsIso (sigmaReflectorRestrictionYonedaUnit β) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaReflectorLeftKan_unit_isIso β hβ
  dsimp only [sigmaReflectorRestrictionYonedaUnit, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr,
    Iso.homCongr_apply, Iso.homCongr, Equiv.coe_fn_mk]
  infer_instance

/-- 概要：専用候補の全前層圏上の単位が指定 Yoneda 単位を延長して存在する。
方針：恒等関手の密度余錐による Hom 制限の全単射を使う。
規約：制限が元の単位そのものである等式を保持する。
使われ方：三角恒等式の右辺を Yoneda 上で計算する。 -/
lemma sigmaReflector_exists_unit :
    ∃ η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)) (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C),
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C))).toFunctor.map η =
        sigmaReflectorYonedaUnit β :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (𝟙 _)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan.presheafIdentity_canonicalColimits (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)).surjective
      (sigmaReflectorYonedaUnit β)

/-- 概要：制限上の指定 Yoneda 単位の逆。
方針：証明済みの可逆性から同じ逆射を取る。
規約：全自然変換の逆を使う。
使われ方：余単位の制限。 -/
def sigmaReflectorRestrictionYonedaInverse :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C ≫ L))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) := by
  have := sigmaReflectorRestrictionYonedaUnit_isIso β hβ
  exact inv (sigmaReflectorRestrictionYonedaUnit β)

include β hβ in
/-- 概要：P_Σ 上の余単位が同じ Yoneda 単位の逆を延長して存在する。
方針：候補の制限が保つ密度余錐による Hom 制限の全単射を使う。
規約：全自然変換と指定逆単位の両立を保持する。
使われ方：包含との随伴の構成。 -/
lemma sigmaReflector_exists_counit :
    ∃ ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C ≫ L) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)),
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C))).toFunctor.map ε =
          sigmaReflectorRestrictionYonedaInverse β hβ := by
  have := sigmaReflectorRestrictionYonedaUnit_isIso β hβ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaReflectorRestriction_canonicalColimits β hβ)
    (𝟙 _)).surjective _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
