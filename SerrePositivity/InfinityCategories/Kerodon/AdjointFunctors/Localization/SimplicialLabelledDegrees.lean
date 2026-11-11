module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledCocone

/-!
# 元の各単体次数における fiber の余極限

概要：元の余極限の fiber の余錐は各次数で型値の余極限である。
方針：評価が元の余極限を保つことと型値の fiber 補題を使う。
規約：元の選ばれた単体集合の余極限と元の標準射を保持する。
使われ方：単体集合としての fiber と余極限の交換。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {X : I ⥤ SSet.{u}} {B : Type u}
  (L : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.Labels X B) (β : B) [HasColimit X]

def degreeLabels (n : SimplexCategoryᵒᵖ) :
    (X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).CoconeTypes where
  pt := B
  ι i x := (L.value i).app n x
  ι_naturality f := by
    funext x
    exact ConcreteCategory.congr_hom (CategoryTheory.congr_app (L.naturality f) n) x

def degreeColimitCocone (n : SimplexCategoryᵒᵖ) :
    (X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).CoconeTypes where
  pt := (colimit X).obj n
  ι i x := (colimit.ι X i).app n x
  ι_naturality f := by
    funext x
    exact ConcreteCategory.congr_hom (CategoryTheory.congr_app (colimit.w X f) n) x

variable [HasColimitsOfShape I (Type u)]

lemma degreeColimit_isColimit (n : SimplexCategoryᵒᵖ) :
    (degreeColimitCocone (X := X) n).IsColimit :=
  (Types.isColimit_iff_coconeTypesIsColimit
    (((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone (colimit.cocone X))).mp
      ⟨isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
        (colimit.isColimit X)⟩

def fiberDegree_isColimit (n : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledCocone.fiberCocone L β)) := by
  apply Nonempty.some
  apply (Types.isColimit_iff_coconeTypesIsColimit _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitCocone.fiberCocone_isColimit (degreeLabels L n) β
    (degreeColimitCocone (X := X) n) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.colimitValue L).app n)
    (fun i x => ConcreteCategory.congr_hom (CategoryTheory.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.ι_colimitValue L i) n) x)
    (degreeColimit_isColimit (X := X) n)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
