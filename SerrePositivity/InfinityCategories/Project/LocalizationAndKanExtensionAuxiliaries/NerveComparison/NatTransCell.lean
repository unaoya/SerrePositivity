module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTrans
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：通常の自然変換を nerve の間の元の QCat の二胞体へ写す。
方針：指定された自然変換の h Fun の射を二胞体の表示同値で戻す。
規約：自然変換は可逆と仮定しない。
使われ方：古典随伴の単位と余単位を QCatAdjunction の入力にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：指定された通常の自然変換を二つの nerve の間の元の QCat の二胞体にする。
方針：構成済みの h Fun の射を二胞体の表示同値で戻す。
規約：両端の一胞体は指定された元の関手の nerve。
使われ方：古典随伴の単位と余単位の二胞体表示。 -/
def nerveNatTransCell {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap G) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom η)

/-- 概要：通常の恒等自然変換の二胞体表示は恒等二胞体。
方針：二胞体の h Fun 表示の単射性と構成済みの恒等射の公式を使う。
規約：元の nerveMap F の恒等射。
使われ方：古典随伴の三角恒等式の移送。 -/
lemma nerveNatTransCell_id {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    nerveNatTransCell (𝟙 F) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap F)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _).injective
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_id F

/-- 概要：通常の自然変換の二胞体表示は垂直合成を保つ。
方針：二胞体の表示同値で h Fun の合成公式へ戻す。
規約：指定された順序の二つの自然変換を扱う。
使われ方：単位・余単位の合成の比較。 -/
lemma nerveNatTransCell_comp {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    nerveNatTransCell (η ≫ θ) = nerveNatTransCell η ≫ nerveNatTransCell θ := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _).injective
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_comp η θ

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
