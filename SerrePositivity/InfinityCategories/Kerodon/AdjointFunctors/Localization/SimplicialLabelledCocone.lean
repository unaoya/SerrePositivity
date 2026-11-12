module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram

/-!
# 元の余極限の値の fiber を頂点とする余錐

概要：各値の fiber から元の余極限の fiber への標準射を作る。
方針：元の標準余錐とラベルの回収式を各次数で使う。
規約：元の標準射により同じ単体を送る。
使われ方：fiber と余極限の交換同型の元の比較射。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledCocone
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {X : I ⥤ SSet.{u}} {B : Type u}
  (L : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.Labels X B) (β : B) [HasColimit X]

def fiberCoconeApp (i : I) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.fiberDiagram L β).obj i ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.colimitValue L) β where
  app n := ↾fun x => ⟨(colimit.ι X i).app n x.val,
    (ConcreteCategory.congr_hom (CategoryTheory.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.ι_colimitValue L i) n) x.val).trans
      x.property⟩
  naturality n m θ := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((colimit.ι X i).naturality θ) x.val

def fiberCocone : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.fiberDiagram L β) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.colimitValue L) β
  ι :=
    { app := fiberCoconeApp L β
      naturality := fun i j f => by
        apply NatTrans.ext
        funext n
        ext x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (CategoryTheory.congr_app (colimit.w X f) n) x.val }

lemma fiberCoconeApp_inclusion (i : I) :
    fiberCoconeApp L β i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.colimitValue L) β =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (L.value i) β ≫ colimit.ι X i := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledCocone
