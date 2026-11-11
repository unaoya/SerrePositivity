module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaInclusionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom

/-!
概要：oriented comma 上の図式間の射を元の添字へ制限し、逆に延長する。
方針：元の添字への射影と普遍な矢印を使って延長し、恒等矢印上で往復を計算する。
規約：元の関手 δ 自体の fibration 性は不要。
使われ方：comma 上の Kan の Hom 普遍性を元の指定変換へ戻す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：comma 上の射を恒等矢印に制限し元の添字上の射へ戻す。
方針：包含で前合成し、両射影の厳密な計算則で端点を輸送する。
規約：端点の同一視を等式の同型で明示する。
使われ方：comma による Hom 対応の制限方向。 -/
def kanLeftCommaHomRestriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G) →
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G) := fun α ↦
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
    (U := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀))
    (V := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G))
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source, Category.id_comp])
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_projection])
    ((hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)).app D)).toFunctor.map α)

/-- 概要：元の添字上の射を comma の普遍矢印に沿って延長する。
方針：元の添字への射影で前合成してから、普遍矢印の G による像を合成する。
規約：変換の類を入力とし、代表を選び直さない。
使われ方：comma による Hom 対応の逆方向。 -/
def kanLeftCommaHomExtension {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G) :=
  (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ)).app D)).toFunctor.map β ≫
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ) G))

/-- 概要：普遍矢印による延長を恒等矢印へ制限すると元の射を回収する。
方針：包含と元の添字への射影の合成、普遍矢印の包含上の定値性を使う。
規約：元の指定された h Fun の射そのものとの等式。
使われ方：comma の Hom 制限の全射性。 -/
lemma kanLeftCommaHomRestriction_extension {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G)) :
    kanLeftCommaHomRestriction δ F₀ G (kanLeftCommaHomExtension δ F₀ G β) = β := by
  have hp : (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)).app D)).toFunctor = 𝟭 _ := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source, pre_id,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  have hh := CategoryTheory.Functor.congr_hom hp β
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ) ≫ G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G) := by
    simp only [Category.assoc, reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source δ),
      reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_projection δ)]
  have hc : (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)).app D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ) G))) =
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) he) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
    refine _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom _ he ?_
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).h ≫ G =
      fst K (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ ≫ G
    rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy_inclusion_h δ),
      reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source δ)]
  simp only [kanLeftCommaHomRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, kanLeftCommaHomExtension, CategoryTheory.Functor.map_comp]
  erw [hc, hh]
  simp only [Category.assoc, eqToHom_trans]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：同じ raw なホモトピーの類は両端の等式による輸送と整合する。
方針：代表辺の一次単体を比較し、両端の輸送の公式を用いる。
規約：ホモトピーの quasicategory 性や可逆性は不要。
使われ方：comma の比較を射影したホモトピーの類の計算。 -/
lemma kanHomotopyHom_transport {A D : SSet.{u}} {f g f' g' : A ⟶ D}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (hf : f = f') (hg : g = g')
    (hh : H.h = H'.h) :
    eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hf).symm ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ≫
          eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hg) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hf) (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hg)
  change SSet.yonedaEquiv (curry H.h) = SSet.yonedaEquiv (curry H'.h)
  rw [hh]

/-- 概要：comma の射を恒等矢印に制限して延長し直すと元の射を回収する。
方針：恒等矢印から各矢印への比較の自然性と元の添字が固定されることを使う。
規約：射は h Fun の任意の射。
使われ方：comma の Hom 制限の単射性。 -/
lemma kanLeftCommaHomExtension_restriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G)) :
    kanLeftCommaHomExtension δ F₀ G (kanLeftCommaHomRestriction δ F₀ G α) = α := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaIdentityComparison δ
  have h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftComma δ) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) := by
    simp only [Category.assoc, reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source δ), Category.id_comp]
  have h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G) = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ) ≫ G := by
    rw [Category.assoc, reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_projection δ), Category.assoc]
  have hc₀ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀)) h₀ (by
      change T.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀ =
        fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftComma δ) (Δ[1] : SSet.{u}) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀)
      rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaIdentityComparison_source δ)]
      simp only [Category.assoc, reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source δ)])
  have hc₁ := kanHomotopyHom_transport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ) G) h₁ rfl (by
      change T.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).h ≫ G
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaIdentityComparison_projection])
  simp only [eqToHom_refl, Category.comp_id] at hc₁
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans T D).naturality α
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app, hc₀] at hn
  have hp : (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ)).app D)).toFunctor =
        (hoFunctor.map
          ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  have hh := CategoryTheory.Functor.congr_hom hp α
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  simp only [kanLeftCommaHomExtension, kanLeftCommaHomRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr,
    Iso.homCongr_apply, eqToIso.inv, eqToIso.hom, CategoryTheory.Functor.map_comp, eqToHom_map]
  erw [hh]
  rw [← hc₁]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [hn]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hid : (hoFunctor.map ((pre (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftComma δ))).app D)).toFunctor = 𝟭 _ := by
    rw [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  have hi := CategoryTheory.Functor.congr_hom hid α
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hi
  exact hi

/-- 概要：comma 上の射と元の添字上の射の厳密な Hom 全単射。
方針：恒等矢印への制限と普遍矢印による延長の両逆を束ねる。
規約：全ての単体集合に quasicategory 性は不要。
使われ方：任意の δ の Kan 拡張の Hom 普遍性への還元。 -/
def kanLeftCommaHomEquiv {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G) where
  toFun := kanLeftCommaHomRestriction δ F₀ G
  invFun := kanLeftCommaHomExtension δ F₀ G
  left_inv := kanLeftCommaHomExtension_restriction δ F₀ G
  right_inv := kanLeftCommaHomRestriction_extension δ F₀ G

/-- 概要：comma の Hom 制限は底図式間の射による後合成に自然。
方針：底射影と恒等矢印の包含の合成が δ であることをホモトピー圏へ移す。
規約：τ の可逆性は不要。
使われ方：comma 上の Kan の比較写像と元の比較写像の同定。 -/
lemma kanLeftCommaHomRestriction_comp {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) {G G' : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ G))
    (τ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G G') :
    kanLeftCommaHomRestriction δ F₀ G'
        (α ≫ (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ)).app D)).toFunctor.map τ) =
      kanLeftCommaHomRestriction δ F₀ G α ≫ (hoFunctor.map ((pre δ).app D)).toFunctor.map τ := by
  have hp : (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)).app D)).toFunctor =
        (hoFunctor.map ((pre δ).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_projection]
  have hh := CategoryTheory.Functor.congr_hom hp τ
  simp only [kanLeftCommaHomRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hh]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
