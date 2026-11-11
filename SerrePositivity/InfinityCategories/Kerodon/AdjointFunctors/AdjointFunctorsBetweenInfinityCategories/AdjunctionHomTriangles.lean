module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitLeftTriangle

/-!
概要：QCat の随伴の三角恒等式を元の関手圏の h の式へ移す。
方針：zigzag の前後合成表示と厳密な単位子を使う。
規約：写像空間の各点だけでなく h Fun の全体の等式を得る。
使われ方：B5 の随伴の反映。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

local instance adjunctionHomTrianglesHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：随伴の左三角恒等式を h Fun の前後合成の式として読む。
方針：双圏の三角恒等式と zigzag の表示を合わせ単位子を消す。
規約：指定された単位と余単位の類を使う。
使われ方：通常の圏への随伴の反映。 -/
lemma adjunction_leftTriangleHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag a.unitHom a.counitHom =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := by
  have h := a.left_triangle_hom
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatLeftZigzag_hom a.unitHom a.counitHom
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.unitHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.counitHom, Equiv.symm_apply_apply] at he
  erw [he] at h
  simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv] at h
  exact h.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F))

/-- 概要：随伴の右三角恒等式を h Fun の前後合成の式として読む。
方針：右 zigzag の表示と単位子の厳密性を使う。
規約：元の指定された二胞体を使う。
使われ方：古典随伴の右三角恒等式の復元。 -/
lemma adjunction_rightTriangleHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) :
    (hoFunctor.map ((pre G).app X)).toFunctor.map a.unitHom ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map a.counitHom =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  have h := a.right_triangle_hom
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatRightZigzag_hom a.unitHom a.counitHom
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.unitHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.counitHom, Equiv.symm_apply_apply] at he
  erw [he] at h
  simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv] at h
  exact h.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
