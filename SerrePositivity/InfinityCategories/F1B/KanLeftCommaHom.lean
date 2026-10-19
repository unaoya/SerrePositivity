module

public import SerrePositivity.InfinityCategories.F1B.KanLeftCommaInclusionHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinRightHom

/-!
概要：oriented comma 上の図式間の射を元の添字へ制限し、逆に延長する。
方針：元の添字への射影と普遍な矢印を使って延長し、恒等矢印上で往復を計算する。
規約：元の関手 δ 自体の fibration 性は不要。
使われ方：comma 上の Kan の Hom 普遍性を元の指定変換へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：comma 上の射を恒等矢印に制限し元の添字上の射へ戻す。
方針：包含で前合成し、両射影の厳密な計算則で端点を輸送する。
規約：端点の同一視を等式の同型で明示する。
使われ方：comma による Hom 対応の制限方向。 -/
def kanLeftCommaHomRestriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) :
    FunctorHom (kanLeftCommaSource δ ≫ F₀) (kanLeftCommaProjection δ ≫ G) →
      FunctorHom F₀ (δ ≫ G) := fun α ↦
  kanFunctorHomCongr
    (U := kanLeftCommaInclusion δ ≫ (kanLeftCommaSource δ ≫ F₀))
    (V := kanLeftCommaInclusion δ ≫ (kanLeftCommaProjection δ ≫ G))
    (by rw [← Category.assoc, kanLeftCommaInclusion_source, Category.id_comp])
    (by rw [← Category.assoc, kanLeftCommaInclusion_projection])
    ((hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor.map α)

/-- 概要：元の添字上の射を comma の普遍矢印に沿って延長する。
方針：元の添字への射影で前合成してから、普遍矢印の G による像を合成する。
規約：変換の類を入力とし、代表を選び直さない。
使われ方：comma による Hom 対応の逆方向。 -/
def kanLeftCommaHomExtension {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) (β : FunctorHom F₀ (δ ≫ G)) :
    FunctorHom (kanLeftCommaSource δ ≫ F₀) (kanLeftCommaProjection δ ≫ G) :=
  (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.map β ≫
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp (kanLeftCommaHomotopy δ) G))

/-- 概要：普遍矢印による延長を恒等矢印へ制限すると元の射を回収する。
方針：包含と元の添字への射影の合成、普遍矢印の包含上の定値性を使う。
規約：元の指定された h Fun の射そのものとの等式。
使われ方：comma の Hom 制限の全射性。 -/
lemma kanLeftCommaHomRestriction_extension {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D) (β : FunctorHom F₀ (δ ≫ G)) :
    kanLeftCommaHomRestriction δ F₀ G (kanLeftCommaHomExtension δ F₀ G β) = β := by
  have hp : (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor = 𝟭 _ := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, kanLeftCommaInclusion_source, pre_id,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  have hh := CategoryTheory.Functor.congr_hom hp β
  have he : kanLeftCommaInclusion δ ≫ ((kanLeftCommaSource δ ≫ δ) ≫ G) =
      kanLeftCommaInclusion δ ≫ (kanLeftCommaProjection δ ≫ G) := by
    simp only [Category.assoc, reassoc_of% (kanLeftCommaInclusion_source δ),
      reassoc_of% (kanLeftCommaInclusion_projection δ)]
  have hc : (hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp (kanLeftCommaHomotopy δ) G))) =
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q)) he) := by
    rw [← functorHomotopyPrecomp_hom]
    refine kanHomotopyHom_eqToHom _ he ?_
    change (kanLeftCommaInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ (kanLeftCommaHomotopy δ).h ≫ G =
      fst K (Δ[1] : SSet.{u}) ≫ kanLeftCommaInclusion δ ≫ kanLeftCommaSource δ ≫ δ ≫ G
    rw [reassoc_of% (kanLeftCommaHomotopy_inclusion_h δ),
      reassoc_of% (kanLeftCommaInclusion_source δ)]
  simp only [kanLeftCommaHomRestriction, kanFunctorHomCongr, Iso.homCongr_apply,
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
    eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q)) hf).symm ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) ≫
          eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q)) hg) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H') := by
  apply homMk_transport (congrArg functorVertex hf) (congrArg functorVertex hg)
  change SSet.yonedaEquiv (curry H.h) = SSet.yonedaEquiv (curry H'.h)
  rw [hh]

/-- 概要：comma の射を恒等矢印に制限して延長し直すと元の射を回収する。
方針：恒等矢印から各矢印への比較の自然性と元の添字が固定されることを使う。
規約：射は h Fun の任意の射。
使われ方：comma の Hom 制限の単射性。 -/
lemma kanLeftCommaHomExtension_restriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (G : C ⟶ D)
    (α : FunctorHom (kanLeftCommaSource δ ≫ F₀) (kanLeftCommaProjection δ ≫ G)) :
    kanLeftCommaHomExtension δ F₀ G (kanLeftCommaHomRestriction δ F₀ G α) = α := by
  let T := kanLeftCommaIdentityComparison δ
  have h₀ : (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ) ≫
      (kanLeftCommaSource δ ≫ F₀) = 𝟙 (kanLeftComma δ) ≫ (kanLeftCommaSource δ ≫ F₀) := by
    simp only [Category.assoc, reassoc_of% (kanLeftCommaInclusion_source δ), Category.id_comp]
  have h₁ : (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ) ≫
      (kanLeftCommaProjection δ ≫ G) = (kanLeftCommaSource δ ≫ δ) ≫ G := by
    rw [Category.assoc, reassoc_of% (kanLeftCommaInclusion_projection δ), Category.assoc]
  have hc₀ := kanHomotopyHom_eqToHom
    (functorHomotopyPostcomp T (kanLeftCommaSource δ ≫ F₀)) h₀ (by
      change T.h ≫ kanLeftCommaSource δ ≫ F₀ =
        fst (kanLeftComma δ) (Δ[1] : SSet.{u}) ≫
          (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ) ≫ (kanLeftCommaSource δ ≫ F₀)
      rw [reassoc_of% (kanLeftCommaIdentityComparison_source δ)]
      simp only [Category.assoc, reassoc_of% (kanLeftCommaInclusion_source δ)])
  have hc₁ := kanHomotopyHom_transport
    (functorHomotopyPostcomp T (kanLeftCommaProjection δ ≫ G))
    (functorHomotopyPostcomp (kanLeftCommaHomotopy δ) G) h₁ rfl (by
      change T.h ≫ kanLeftCommaProjection δ ≫ G = (kanLeftCommaHomotopy δ).h ≫ G
      rw [← Category.assoc, kanLeftCommaIdentityComparison_projection])
  simp only [eqToHom_refl, Category.comp_id] at hc₁
  have hn := (kanPrecompositionNatTrans T D).naturality α
  rw [kanPrecompositionNatTrans_app, kanPrecompositionNatTrans_app, hc₀] at hn
  have hp : (hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor =
        (hoFunctor.map
          ((pre (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  have hh := CategoryTheory.Functor.congr_hom hp α
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  simp only [kanLeftCommaHomExtension, kanLeftCommaHomRestriction, kanFunctorHomCongr,
    Iso.homCongr_apply, eqToIso.inv, eqToIso.hom, CategoryTheory.Functor.map_comp, eqToHom_map]
  erw [hh]
  rw [← hc₁]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [hn]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hid : (hoFunctor.map ((pre (𝟙 (kanLeftComma δ))).app D)).toFunctor = 𝟭 _ := by
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
    FunctorHom (kanLeftCommaSource δ ≫ F₀) (kanLeftCommaProjection δ ≫ G) ≃
      FunctorHom F₀ (δ ≫ G) where
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
    (α : FunctorHom (kanLeftCommaSource δ ≫ F₀) (kanLeftCommaProjection δ ≫ G))
    (τ : FunctorHom G G') :
    kanLeftCommaHomRestriction δ F₀ G'
        (α ≫ (hoFunctor.map ((pre (kanLeftCommaProjection δ)).app D)).toFunctor.map τ) =
      kanLeftCommaHomRestriction δ F₀ G α ≫ (hoFunctor.map ((pre δ).app D)).toFunctor.map τ := by
  have hp : (hoFunctor.map ((pre (kanLeftCommaProjection δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor =
        (hoFunctor.map ((pre δ).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, kanLeftCommaInclusion_projection]
  have hh := CategoryTheory.Functor.congr_hom hp τ
  simp only [kanLeftCommaHomRestriction, kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hh]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.F1B
