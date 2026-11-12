module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransWhiskering
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransCell
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitLeftTriangle

/-!
概要：通常の圏の指定された随伴を nerve 間の元の QCat の随伴へ移す。
方針：指定単位・余単位を二胞体へ写し、左右の whiskering と合成の保存で三角恒等式を移す。
規約：hC と hD の間だけの随伴ではなく元の nerve 間の QCatAdjunction を構成する。
使われ方：B5 の古典随伴の nerve による回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：通常の圏の随伴は指定された nerve 間の QCat の随伴を与える。
方針：単位と余単位の辺の類に、左右 whiskering と垂直合成の保存を適用する。
規約：通常の単位・余単位を選び直さない。
使われ方：古典随伴の nerve への移送の順方向。 -/
def nerveAdjunctionOfAdjunction {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (nerveMap F) (nerveMap G) := by
  let η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (nerve C)) (nerveMap F ≫ nerveMap G) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := 𝟭 C) (G := F ⋙ G) a.unit
  let ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap G ≫ nerveMap F) (𝟙 (nerve D)) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := G ⋙ F) (G := 𝟭 D) a.counit
  have hL : CategoryTheory.Functor.whiskerRight a.unit F ≫
      CategoryTheory.Functor.whiskerLeft F a.counit = 𝟙 F := by
    ext x
    exact a.left_triangle_components x
  have hR : CategoryTheory.Functor.whiskerLeft G a.unit ≫
      CategoryTheory.Functor.whiskerRight a.counit G = 𝟙 G := by
    ext x
    exact a.right_triangle_components x
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.mkOfHomTriangles ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _).symm η)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _).symm ε) ?_ ?_
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatLeftZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε = _
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε = 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F))) := by
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag, η, ε]
      rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerLeft,
        ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_comp, hL]
      exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_id F
    exact ht.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor (nerve C) (nerve D)).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap F))).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatRightZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    have ht : (hoFunctor.map ((pre (nerveMap G)).app (nerve C))).toFunctor.map η ≫
        (hoFunctor.map ((ihom (nerve D)).map (nerveMap G))).toFunctor.map ε =
          𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap G))) := by
      dsimp only [η, ε]
      rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerRight,
        ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_comp, hR]
      exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_id G
    exact ht.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor (nerve D) (nerve C)).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap G))).symm

/-- 概要：構成した nerve の随伴の単位は元の指定単位の表示に等しい。
方針：三角恒等式からの構成の単位フィールドを読む。
規約：単位を同型で取り替えない。
使われ方：古典随伴の指定データの保存。 -/
lemma nerveAdjunctionOfAdjunction_unitHom {C D : Type u}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    (nerveAdjunctionOfAdjunction a).unitHom =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := 𝟭 C) (G := F ⋙ G) a.unit := rfl

/-- 概要：構成した nerve の随伴の余単位は元の指定余単位の表示に等しい。
方針：構成の余単位フィールドの表示を取る。
規約：指定された余単位を保存する射の等式。
使われ方：随伴の古典比較の両端の整合。 -/
lemma nerveAdjunctionOfAdjunction_counitHom {C D : Type u}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    (nerveAdjunctionOfAdjunction a).counitHom =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := G ⋙ F) (G := 𝟭 D) a.counit := rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
