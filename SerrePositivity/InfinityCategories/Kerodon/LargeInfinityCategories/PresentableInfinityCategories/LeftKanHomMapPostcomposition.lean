module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomWhiskerInterchange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomPrecompositionLaws
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.UniversalProperty

/-!
概要：指定左 Kan 比較の単位回収写像を同じ後合成で運ぶ。
方針：射作用の合成保存と前後合成の交換則を使う。
規約：元の単位と比較射を保持する。使われ方：E01 の点評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LimitsAndColimits.KanExtensions
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：後合成の端点正規化を同じ射作用に戻す。
方針：恒等な端点移送を消す。規約：指定射を保持。
使われ方：単位回収式の計算。 -/
lemma postcomposeFunctorHom_eq_map {A X Y : SSet.{u}}
    (q : X ⟶ Y) {F G : A ⟶ X} (α : FunctorHom F G) :
    postcomposeFunctorHom q α =
      (hoFunctor.map ((ihom A).map q)).toFunctor.map α := by
  simp only [postcomposeFunctorHom, normalizedVertexHomMap, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- 概要：同じ左 Kan の単位回収式を後合成で運ぶ。
方針：射作用の合成保存と前後合成交換を使う。
規約：任意の単位と元の比較射を変更しない。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3 の
指定 Yoneda 比較を点評価する計算法則。 -/
lemma leftKanHomMap_postcompose_heq {K C D E : SSet.{u}}
    (δ : K ⟶ C) (q : D ⟶ E) {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : FunctorHom F₀ (δ ≫ F)) (η : FunctorHom F G) :
    HEq (postcomposeFunctorHom q (leftKanHomMap δ β G η))
      (leftKanHomMap δ
        (kanFunctorHomCongr rfl (Category.assoc δ F q) (postcomposeFunctorHom q β))
        (G ≫ q) (postcomposeFunctorHom q η)) := by
  unfold leftKanHomMap
  simp only [postcomposeFunctorHom_eq_map, Functor.map_comp,
    kanFunctorHomCongr, Iso.homCongr_apply, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]
  have h := postcompose_precomposeFunctorHom_heq δ q η
  simp only [postcomposeFunctorHom_eq_map, precomposeFunctorHom_eq_map] at h
  apply heq_of_eq
  exact congrArg (fun z =>
    (hoFunctor.map ((ihom K).map q)).toFunctor.map β ≫ z) (eq_of_heq h)

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
