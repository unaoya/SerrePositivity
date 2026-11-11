module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitCocone
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# ラベル付き単体集合値図式の fiber の図式

概要：元の各単体集合の値の fiber を元の遷移写像で束ねる。
方針：元のラベルへの自然性と fiber の包含を使う。
規約：添字圏の全射と全単体作用素を保持する。
使われ方：元の hammock 上の値の fiber の余極限表示。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ SSet.{u}) (B : Type u)

structure Labels where
  value : ∀ i, X.obj i ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B
  naturality : ∀ {i j} (f : i ⟶ j), X.map f ≫ value j = value i

variable {X B} (L : Labels X B) (β : B)

def fiberDiagram : I ⥤ SSet.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (L.value i) β
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.map _ β _ (X.map f) (L.naturality f)
  map_id i := by
    apply NatTrans.ext
    funext n
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (CategoryTheory.congr_app (X.map_id i) n) x.val
  map_comp f g := by
    apply NatTrans.ext
    funext n
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (CategoryTheory.congr_app (X.map_comp f g) n) x.val

def valueCocone : Cocone X where
  pt := (Functor.const SimplexCategoryᵒᵖ).obj B
  ι :=
    { app := L.value
      naturality := fun i _ f => (L.naturality f).trans (Category.comp_id (L.value i)).symm }

def fiberInclusion : fiberDiagram L β ⟶ X where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (L.value i) β
  naturality i j f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.map_inclusion (L.value i) β (L.value j)
    (X.map f) (L.naturality f)

variable [HasColimit X]

def colimitValue : colimit X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B :=
  colimit.desc X (valueCocone L)

lemma ι_colimitValue (i : I) : colimit.ι X i ≫ colimitValue L = L.value i :=
  colimit.ι_desc (valueCocone L) i

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram
