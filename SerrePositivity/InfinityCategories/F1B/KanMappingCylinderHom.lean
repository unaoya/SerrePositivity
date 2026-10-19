module

public import SerrePositivity.InfinityCategories.F1B.KanMappingCylinderContraction
public import SerrePositivity.InfinityCategories.F1B.KanPrecompositionHomotopy
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：写像円柱の右端への制限と底射影による前合成の Hom 対応。
方針：右端への変形を単位とし、固定された右端と底射影から三角恒等式を得る。
規約：写像円柱自身の quasicategory 性は使わない。
使われ方：相対 join の右端への Hom 対応への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：右端への制限と底射影による前合成の合成への単位。
方針：写像円柱の単位の豊穣前合成作用をホモトピー圏へ移す。
規約：標的に quasicategory 性は不要。
使われ方：右端への Hom 対応の逆写像。 -/
def kanMappingCylinderPrecompositionUnit {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    𝟭 (hoFunctor.obj ((ihom (pushout (prismEndpoint 1 K) p)).obj D)) ⟶
      (hoFunctor.map ((pre (pushout.inr (prismEndpoint 1 K) p)).app D)).toFunctor ⋙
        (hoFunctor.map ((pre (mappingCylinderBaseProjection p)).app D)).toFunctor :=
  eqToHom (by
    simp only [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Cat.Hom.id_toFunctor]) ≫
    kanPrecompositionNatTrans (kanMappingCylinderUnit p) D ≫ eqToHom (by
      simp only [pre_map, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
        Cat.Hom.comp_toFunctor])

/-- 概要：底射影で前合成して右端へ制限する合成は厳密な恒等関手。
方針：右包含と底射影の合成の等式を前合成へ移す。
規約：元の関手とその射を同時に保つ。
使われ方：右端への Hom 対応の余単位。 -/
lemma kanMappingCylinderPrecomposition_retraction {K C : SSet.{u}}
    (p : K ⟶ C) (D : SSet.{u}) :
    (hoFunctor.map ((pre (mappingCylinderBaseProjection p)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (pushout.inr (prismEndpoint 1 K) p)).app D)).toFunctor = 𝟭 _ := by
  rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app, ← pre_map,
    mappingCylinderBaseProjection_inr, pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Cat.Hom.id_toFunctor]

/-- 概要：前合成の単位の成分は円柱の変形を U で写した辺の類。
方針：前合成作用の自然変換の成分公式を恒等射と合成の同一視へ移す。
規約：元の円柱の変形を代表として保持する。
使われ方：三角恒等式の計算。 -/
lemma kanMappingCylinderPrecompositionUnit_app {K C D : SSet.{u}} (p : K ⟶ C)
    (U : pushout (prismEndpoint 1 K) p ⟶ D) :
    (kanMappingCylinderPrecompositionUnit p D).app (HomotopyCategory.mk (functorVertex U)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy
          (functorHomotopyPostcomp (kanMappingCylinderUnit p) U)) := by
  unfold kanMappingCylinderPrecompositionUnit
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact kanPrecompositionNatTrans_app (kanMappingCylinderUnit p) U

/-- 概要：円柱の右端への制限は底射影による前合成の左随伴。
方針：変形の単位と厳密な引き戻しの余単位を使い、固定部分で両三角恒等式を計算する。
規約：ホモトピー圏の随伴を構成し、円柱自身の quasicategory 性は要求しない。
使われ方：右端への Hom 対応の構成。 -/
def kanMappingCylinderPrecompositionAdjunction {K C : SSet.{u}}
    (p : K ⟶ C) (D : SSet.{u}) :
    (hoFunctor.map ((pre (pushout.inr (prismEndpoint 1 K) p)).app D)).toFunctor ⊣
      (hoFunctor.map ((pre (mappingCylinderBaseProjection p)).app D)).toFunctor where
  unit := kanMappingCylinderPrecompositionUnit p D
  counit := eqToHom (kanMappingCylinderPrecomposition_retraction p D)
  left_triangle_components x := by
    obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨U, rfl⟩ := (functorVertexEquiv _ D).surjective v
    change (hoFunctor.map ((pre (pushout.inr (prismEndpoint 1 K) p)).app D)).toFunctor.map
      ((kanMappingCylinderPrecompositionUnit p D).app
        (HomotopyCategory.mk (functorVertex U))) ≫ _ = 𝟙 _
    rw [kanMappingCylinderPrecompositionUnit_app]
    simp only [eqToHom_app]
    rw [← functorHomotopyPrecomp_hom]
    rw [kanHomotopyHom_eqToHom _ (by
      simp only [Category.assoc, reassoc_of% (mappingCylinderBaseProjection_inr p),
        Category.id_comp]) (by
      change (pushout.inr (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
          (kanMappingCylinderContraction p ≫ U) = _
      rw [← Category.assoc, kanMappingCylinderContraction_inr, Category.assoc]
      rfl)]
    simp
  right_triangle_components y := by
    obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨G, rfl⟩ := (functorVertexEquiv _ D).surjective v
    change (kanMappingCylinderPrecompositionUnit p D).app
      (HomotopyCategory.mk (functorVertex (mappingCylinderBaseProjection p ≫ G))) ≫ _ = 𝟙 _
    rw [kanMappingCylinderPrecompositionUnit_app]
    simp only [eqToHom_app, eqToHom_map]
    rw [kanHomotopyHom_eqToHom _ (by
      simp only [Category.assoc, reassoc_of% (mappingCylinderBaseProjection_inr p),
        Category.id_comp]) (by
      change kanMappingCylinderContraction p ≫ (mappingCylinderBaseProjection p ≫ G) = _
      rw [← Category.assoc, kanMappingCylinderContraction_baseProjection, Category.assoc]
      rfl)]
    simp

/-- 概要：円柱の図式から底射影に沿う図式への射は右端上の射と一対一に対応する。
方針：前合成の随伴の Hom 全単射を、関手頂点の表示で取り出す。
規約：始域・標的の quasicategory 性を仮定しない。
使われ方：相対 join の右端への Hom 対応の移送。 -/
def kanMappingCylinderHomEquiv {K C D : SSet.{u}} (p : K ⟶ C)
    (H : pushout (prismEndpoint 1 K) p ⟶ D) (G : C ⟶ D) :
    FunctorHom H (mappingCylinderBaseProjection p ≫ G) ≃
      FunctorHom (pushout.inr (prismEndpoint 1 K) p ≫ H) G :=
  ((kanMappingCylinderPrecompositionAdjunction p D).homEquiv
    (HomotopyCategory.mk (functorVertex H)) (HomotopyCategory.mk (functorVertex G))).symm

/-- 概要：円柱の Hom 対応は右端への制限と、底射影の厳密な引き戻しの同一視で与えられる。
方針：随伴の Hom 全単射の逆方向の公式を展開する。
規約：端点の同一視は eqToHom で明示する。
使われ方：元の Kan 変換の Hom 公式との比較。 -/
lemma kanMappingCylinderHomEquiv_apply {K C D : SSet.{u}} (p : K ⟶ C)
    (H : pushout (prismEndpoint 1 K) p ⟶ D) (G : C ⟶ D)
    (α : FunctorHom H (mappingCylinderBaseProjection p ≫ G)) :
    kanMappingCylinderHomEquiv p H G α =
      (hoFunctor.map ((pre (pushout.inr (prismEndpoint 1 K) p)).app D)).toFunctor.map α ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
          (show pushout.inr (prismEndpoint 1 K) p ≫ (mappingCylinderBaseProjection p ≫ G) = G by
            rw [← Category.assoc, mappingCylinderBaseProjection_inr, Category.id_comp])) := by
  change _ ≫ (eqToHom (kanMappingCylinderPrecomposition_retraction p D)).app
    (HomotopyCategory.mk (functorVertex G)) = _
  rw [eqToHom_app]

end SerrePositivity.InfinityCategories.F1B
