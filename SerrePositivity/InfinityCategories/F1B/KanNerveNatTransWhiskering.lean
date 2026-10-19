module

public import SerrePositivity.InfinityCategories.F1B.KanNerveEdgeHom
public import SerrePositivity.InfinityCategories.F1B.KanNerveFunctorHomCategory
public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransCell
public import SerrePositivity.InfinityCategories.F1B.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.F1B.EnrichedPostcomposition

/-!
概要：通常の自然変換の nerve 表示は左右の whiskering と整合する。
方針：指数比較の前後合成自然性を h の射に適用し、頂点の表示の輸送を消す。
規約：自然変換の可逆性は仮定しない。
使われ方：古典随伴の三角恒等式を QCat の二胞体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：通常の自然変換の後合成は nerve 間の元の関手圏の後合成と一致する。
方針：関手圏の指数比較の自然性を h に写し、指定された辺の類で評価する。
規約：同じ元の合成関手を両端に持つ射の等式。
使われ方：古典随伴の単位を左随伴で後合成する式の移送。 -/
lemma kanNerveNatTransHom_whiskerRight {C D E : Type u}
    [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F G : C ⥤ D} (η : F ⟶ G) (H : D ⥤ E) :
    (hoFunctor.map ((ihom (nerve C)).map (nerveMap H))).toFunctor.map (kanNerveNatTransHom η) =
      kanNerveNatTransHom (whiskerRight η H) := by
  have hh : (hoFunctor.map (kanNerveFunctorCategoryIso C D).hom).toFunctor ⋙
      (hoFunctor.map ((ihom (nerve C)).map (nerveMap H))).toFunctor =
      (hoFunctor.map (nerveMap ((whiskeringRight C D E).obj H))).toFunctor ⋙
        (hoFunctor.map (kanNerveFunctorCategoryIso C E).hom).toFunctor := by
    change (hoFunctor.map (kanNerveFunctorCategoryIso C D).hom ≫
      hoFunctor.map ((ihom (nerve C)).map (nerveMap H))).toFunctor = _
    rw [← Functor.map_comp, ← kanNerveFunctorCategoryIso_postcomp, Functor.map_comp]
    rfl
  have hm := CategoryTheory.Functor.congr_hom hh (HomotopyCategory.homMk (nerve.edgeMk η))
  have hn := congrArg (fun m ↦
    (mapHomotopyCategory (kanNerveFunctorCategoryIso C E).hom).map m)
    (kanNerveEdgeHom_map ((whiskeringRight C D E).obj H) η)
  simp only [Functor.comp_map, hoFunctor_map, Functor.toCatHom_toFunctor,
    mapHomotopyCategory_map_homMk] at hm
  simp only [Functor.map_comp, mapHomotopyCategory_map_homMk] at hn
  simp only [kanNerveNatTransHom, Functor.map_comp, hoFunctor_map, Functor.toCatHom_toFunctor,
    mapHomotopyCategory_map_homMk]
  rw [hm]
  erw [← hn]
  simp only [kanNerveFunctorVertexIso, eqToIso.hom, eqToIso.inv,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- 概要：通常の自然変換の前合成は元の nerve 間の関手圏の前合成と一致する。
方針：指数比較の始域の自然性を辺の類で評価して端点の輸送を消す。
規約：始域の関手 I と自然変換を指定する。
使われ方：古典随伴の余単位を左随伴で前合成する式の移送。 -/
lemma kanNerveNatTransHom_whiskerLeft {A C D : Type u}
    [Category.{u} A] [Category.{u} C] [Category.{u} D]
    (I : A ⥤ C) {F G : C ⥤ D} (η : F ⟶ G) :
    (hoFunctor.map ((pre (nerveMap I)).app (nerve D))).toFunctor.map (kanNerveNatTransHom η) =
      kanNerveNatTransHom (whiskerLeft I η) := by
  have hh : (hoFunctor.map (kanNerveFunctorCategoryIso C D).hom).toFunctor ⋙
      (hoFunctor.map ((pre (nerveMap I)).app (nerve D))).toFunctor =
      (hoFunctor.map (nerveMap ((whiskeringLeft A C D).obj I))).toFunctor ⋙
        (hoFunctor.map (kanNerveFunctorCategoryIso A D).hom).toFunctor := by
    change (hoFunctor.map (kanNerveFunctorCategoryIso C D).hom ≫
      hoFunctor.map ((pre (nerveMap I)).app (nerve D))).toFunctor = _
    rw [← Functor.map_comp, ← kanNerveFunctorCategoryIso_precomp, Functor.map_comp]
    rfl
  have hm := CategoryTheory.Functor.congr_hom hh (HomotopyCategory.homMk (nerve.edgeMk η))
  have hn := congrArg (fun m ↦
    (mapHomotopyCategory (kanNerveFunctorCategoryIso A D).hom).map m)
    (kanNerveEdgeHom_map ((whiskeringLeft A C D).obj I) η)
  simp only [Functor.comp_map, hoFunctor_map, Functor.toCatHom_toFunctor,
    mapHomotopyCategory_map_homMk] at hm
  simp only [Functor.map_comp, mapHomotopyCategory_map_homMk] at hn
  simp only [kanNerveNatTransHom, Functor.map_comp, hoFunctor_map, Functor.toCatHom_toFunctor,
    mapHomotopyCategory_map_homMk]
  rw [hm]
  erw [← hn]
  simp only [kanNerveFunctorVertexIso, eqToIso.hom, eqToIso.inv,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

section Cells
open Bicategory
local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：自然変換の二胞体表示は右 whiskering を保つ。
方針：h Fun の後合成の公式を二胞体の表示同値で戻す。
規約：右に合成する通常の関手 H を指定する。
使われ方：古典随伴の単位の二胞体としての自然性。 -/
lemma kanNerveNatTransCell_whiskerRight {C D E : Type u}
    [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F G : C ⥤ D} (η : F ⟶ G) (H : D ⥤ E) :
    kanNerveNatTransCell η ▷ qcatMap (nerveMap H) =
      kanNerveNatTransCell (CategoryTheory.Functor.whiskerRight η H) := by
  apply (qcatCellEquiv _ _).injective
  rw [qcatCell_whiskerRight]
  exact kanNerveNatTransHom_whiskerRight η H

/-- 概要：自然変換の二胞体表示は左 whiskering を保つ。
方針：前合成の h Fun 作用の公式に表示同値の単射性を使う。
規約：始域の通常の関手 I と自然変換 η を指定する。
使われ方：古典随伴の余単位の二胞体としての自然性。 -/
lemma kanNerveNatTransCell_whiskerLeft {A C D : Type u}
    [Category.{u} A] [Category.{u} C] [Category.{u} D]
    (I : A ⥤ C) {F G : C ⥤ D} (η : F ⟶ G) :
    qcatMap (nerveMap I) ◁ kanNerveNatTransCell η =
      kanNerveNatTransCell (CategoryTheory.Functor.whiskerLeft I η) := by
  apply (qcatCellEquiv _ _).injective
  rw [qcatCell_whiskerLeft]
  exact kanNerveNatTransHom_whiskerLeft I η

end Cells

end SerrePositivity.InfinityCategories.F1B
