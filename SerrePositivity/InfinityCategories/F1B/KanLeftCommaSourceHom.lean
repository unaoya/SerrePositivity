module

public import SerrePositivity.InfinityCategories.F1B.KanLeftCommaHom
public import SerrePositivity.InfinityCategories.F1B.KanPrecompositionFullFaithfulness

/-!
概要：comma の元の添字への射影による前合成は写像空間で充満忠実。
方針：恒等矢印への制限を Hom の逆とし、添字を固定する比較の自然性で両逆を示す。
規約：全ての標的への Hom 対応を証明してから全パラメータ判定を適用する。
使われ方：元の相対制限の標的と comma 側の標的の写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の添字から引き戻した図式間の射を恒等矢印へ制限する。
方針：包含への前合成と射影の切断の等式で端点を揃える。
規約：標的の quasicategory 性を要求しない。
使われ方：comma 射影による Hom の引き戻しの逆写像。 -/
def kanLeftCommaSourceHomRestriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (F G : K ⟶ D) :
    FunctorHom (kanLeftCommaSource δ ≫ F) (kanLeftCommaSource δ ≫ G) → FunctorHom F G :=
  fun α ↦ kanFunctorHomCongr
    (U := kanLeftCommaInclusion δ ≫ (kanLeftCommaSource δ ≫ F))
    (V := kanLeftCommaInclusion δ ≫ (kanLeftCommaSource δ ≫ G))
    (by rw [← Category.assoc, kanLeftCommaInclusion_source, Category.id_comp])
    (by rw [← Category.assoc, kanLeftCommaInclusion_source, Category.id_comp])
    ((hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor.map α)

/-- 概要：元の添字の射を引き戻して恒等矢印へ制限すると元の射に戻る。
方針：射影の切断の等式を h Fun の前合成へ移す。
規約：指定された Hom の射そのものを回収する。
使われ方：comma 射影の Hom への作用の単射性。 -/
lemma kanLeftCommaSourceHomRestriction_map {K C D : SSet.{u}} (δ : K ⟶ C)
    (F G : K ⟶ D) (α : FunctorHom F G) :
    kanLeftCommaSourceHomRestriction δ F G
      ((hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.map α) = α := by
  have hp : (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor = 𝟭 _ := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, kanLeftCommaInclusion_source, pre_id,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  have hh := CategoryTheory.Functor.congr_hom hp α
  simp only [kanLeftCommaSourceHomRestriction, kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom]
  erw [hh]
  simp

/-- 概要：引き戻した図式間の射を制限して再び引き戻すと元の射に戻る。
方針：元の添字を固定する comma 比較の自然性を、両端の定値性で簡約する。
規約：quasicategory 性や射の可逆性は不要。
使われ方：comma 射影の Hom への作用の全射性。 -/
lemma kanLeftCommaSourceHom_map_restriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (F G : K ⟶ D)
    (α : FunctorHom (kanLeftCommaSource δ ≫ F) (kanLeftCommaSource δ ≫ G)) :
    (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.map
      (kanLeftCommaSourceHomRestriction δ F G α) = α := by
  let T := kanLeftCommaIdentityComparison δ
  have hc (V : K ⟶ D) := kanHomotopyHom_eqToHom
    (functorHomotopyPostcomp T (kanLeftCommaSource δ ≫ V)) (by
      simp only [Category.assoc, reassoc_of% (kanLeftCommaInclusion_source δ),
        Category.id_comp]) (by
      change T.h ≫ kanLeftCommaSource δ ≫ V =
        fst (kanLeftComma δ) (Δ[1] : SSet.{u}) ≫
          (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ) ≫ (kanLeftCommaSource δ ≫ V)
      rw [reassoc_of% (kanLeftCommaIdentityComparison_source δ)]
      simp only [Category.assoc, reassoc_of% (kanLeftCommaInclusion_source δ)])
  have hn := (kanPrecompositionNatTrans T D).naturality α
  rw [kanPrecompositionNatTrans_app, kanPrecompositionNatTrans_app, hc F, hc G] at hn
  have hp : (hoFunctor.map ((pre (kanLeftCommaInclusion δ)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor =
        (hoFunctor.map
          ((pre (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  have hh := CategoryTheory.Functor.congr_hom hp α
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  simp only [kanLeftCommaSourceHomRestriction, kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, CategoryTheory.Functor.map_comp, eqToHom_map]
  erw [hh]
  have hid : (hoFunctor.map ((pre (𝟙 (kanLeftComma δ))).app D)).toFunctor = 𝟭 _ := by
    rw [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  have hi := CategoryTheory.Functor.congr_hom hid α
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hi
  erw [hn]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact hi

/-- 概要：元の添字への射影の前合成は h Fun 上で充満忠実。
方針：全ての対象を関手頂点で表し、制限と引き戻しの両逆を使う。
規約：任意の単体集合を標的とする。
使われ方：全パラメータ判定に渡す全標的での Hom 全単射。 -/
def kanLeftCommaSource_hoFullyFaithful {K C : SSet.{u}} (δ : K ⟶ C) (D : SSet.{u}) :
    (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.FullyFaithful := by
  have hb (a b : hoFunctor.obj ((ihom K).obj D)) : Function.Bijective
      ((hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.map : (a ⟶ b) → _) := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨F, rfl⟩ := (functorVertexEquiv K D).surjective x
    obtain ⟨G, rfl⟩ := (functorVertexEquiv K D).surjective y
    exact ⟨Function.LeftInverse.injective (kanLeftCommaSourceHomRestriction_map δ F G),
      Function.RightInverse.surjective (kanLeftCommaSourceHom_map_restriction δ F G)⟩
  have : (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.Full :=
    ⟨fun {a b} ↦ (hb a b).2⟩
  have : (hoFunctor.map ((pre (kanLeftCommaSource δ)).app D)).toFunctor.Faithful :=
    ⟨fun {a b} ↦ (hb a b).1⟩
  exact CategoryTheory.Functor.FullyFaithful.ofFullyFaithful _

/-- 概要：comma の元の添字への射影による前合成は実際の写像空間で充満忠実。
方針：全標的の Hom 全単射を内部 Hom の交換で全パラメータへ移す。
規約：δ 自体の単射性や fibration 性は不要。
使われ方：元の相対制限と comma 側の制限の標的の比較。 -/
lemma kanLeftCommaSource_pre_isFullyFaithful {K C : SSet.{u}} (δ : K ⟶ C)
    (D : SSet.{u}) [Quasicategory D] :
    IsFullyFaithful ((pre (kanLeftCommaSource δ)).app D) :=
  kanPrecomposition_isFullyFaithful_of_hoFullyFaithful (kanLeftCommaSource δ)
    (fun Z _ ↦ kanLeftCommaSource_hoFullyFaithful δ Z) D

end SerrePositivity.InfinityCategories.F1B
