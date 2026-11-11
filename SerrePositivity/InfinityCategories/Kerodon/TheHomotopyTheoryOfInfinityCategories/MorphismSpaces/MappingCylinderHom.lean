module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingCylinderContraction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：写像円柱の右端への制限と底射影による前合成の Hom 対応。
方針：右端への変形を単位とし、固定された右端と底射影から三角恒等式を得る。
規約：写像円柱自身の quasicategory 性は使わない。
使われ方：相対 join の右端への Hom 対応への移送。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右端への制限と底射影による前合成の合成への単位。
方針：写像円柱の単位の豊穣前合成作用をホモトピー圏へ移す。
規約：標的に quasicategory 性は不要。
使われ方：右端への Hom 対応の逆写像。 -/
def mappingCylinderPrecompositionUnit {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    𝟭 (hoFunctor.obj ((ihom (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).obj D)) ⟶
      (hoFunctor.map ((pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D)).toFunctor ⋙
        (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p)).app D)).toFunctor :=
  eqToHom (by
    simp only [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Cat.Hom.id_toFunctor]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderUnit p) D ≫ eqToHom (by
      simp only [pre_map, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
        Cat.Hom.comp_toFunctor])

/-- 概要：底射影で前合成して右端へ制限する合成は厳密な恒等関手。
方針：右包含と底射影の合成の等式を前合成へ移す。
規約：元の関手とその射を同時に保つ。
使われ方：右端への Hom 対応の余単位。 -/
lemma mappingCylinderPrecomposition_retraction {K C : SSet.{u}}
    (p : K ⟶ C) (D : SSet.{u}) :
    (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D)).toFunctor = 𝟭 _ := by
  rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Cat.Hom.id_toFunctor]

/-- 概要：前合成の単位の成分は円柱の変形を U で写した辺の類。
方針：前合成作用の自然変換の成分公式を恒等射と合成の同一視へ移す。
規約：元の円柱の変形を代表として保持する。
使われ方：三角恒等式の計算。 -/
lemma mappingCylinderPrecompositionUnit_app {K C D : SSet.{u}} (p : K ⟶ C)
    (U : pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ⟶ D) :
    (mappingCylinderPrecompositionUnit p D).app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderUnit p) U)) := by
  unfold mappingCylinderPrecompositionUnit
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderUnit p) U

/-- 概要：円柱の右端への制限は底射影による前合成の左随伴。
方針：変形の単位と厳密な引き戻しの余単位を使い、固定部分で両三角恒等式を計算する。
規約：ホモトピー圏の随伴を構成し、円柱自身の quasicategory 性は要求しない。
使われ方：右端への Hom 対応の構成。 -/
def mappingCylinderPrecompositionAdjunction {K C : SSet.{u}}
    (p : K ⟶ C) (D : SSet.{u}) :
    (hoFunctor.map ((pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D)).toFunctor ⊣
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p)).app D)).toFunctor where
  unit := mappingCylinderPrecompositionUnit p D
  counit := eqToHom (mappingCylinderPrecomposition_retraction p D)
  left_triangle_components x := by
    obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨U, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).surjective v
    change (hoFunctor.map ((pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D)).toFunctor.map
      ((mappingCylinderPrecompositionUnit p D).app
        (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))) ≫ _ = 𝟙 _
    rw [mappingCylinderPrecompositionUnit_app]
    simp only [eqToHom_app]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom _ (by
      simp only [Category.assoc, reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr p),
        Category.id_comp]) (by
      change (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderContraction p ≫ U) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderContraction_inr, Category.assoc]
      rfl)]
    simp
  right_triangle_components y := by
    obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).surjective v
    change (mappingCylinderPrecompositionUnit p D).app
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G))) ≫ _ = 𝟙 _
    rw [mappingCylinderPrecompositionUnit_app]
    simp only [eqToHom_app, eqToHom_map]
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom _ (by
      simp only [Category.assoc, reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr p),
        Category.id_comp]) (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderContraction p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderContraction_baseProjection, Category.assoc]
      rfl)]
    simp

/-- 概要：円柱の図式から底射影に沿う図式への射は右端上の射と一対一に対応する。
方針：前合成の随伴の Hom 全単射を、関手頂点の表示で取り出す。
規約：始域・標的の quasicategory 性を仮定しない。
使われ方：相対 join の右端への Hom 対応の移送。 -/
def mappingCylinderHomEquiv {K C D : SSet.{u}} (p : K ⟶ C)
    (H : pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ⟶ D) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ≫ H) G :=
  ((mappingCylinderPrecompositionAdjunction p D).homEquiv
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))).symm

/-- 概要：円柱の Hom 対応は右端への制限と、底射影の厳密な引き戻しの同一視で与えられる。
方針：随伴の Hom 全単射の逆方向の公式を展開する。
規約：端点の同一視は eqToHom で明示する。
使われ方：元の Kan 変換の Hom 公式との比較。 -/
lemma mappingCylinderHomEquiv_apply {K C D : SSet.{u}} (p : K ⟶ C)
    (H : pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ⟶ D) (G : C ⟶ D)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G)) :
    mappingCylinderHomEquiv p H G α =
      (hoFunctor.map ((pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D)).toFunctor.map α ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q))
          (show pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G) = G by
            rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.id_comp])) := by
  change _ ≫ (eqToHom (mappingCylinderPrecomposition_retraction p D)).app
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) = _
  rw [eqToHom_app]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
