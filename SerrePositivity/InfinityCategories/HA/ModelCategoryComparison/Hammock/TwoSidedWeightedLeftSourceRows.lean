module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElementsOpposite
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftMap
public import SerrePositivity.KST.ProExcision.NerveOppositeIso
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction

/-!
# 元の重み付き左 bar と反対側の一方向 bar の二重単体的同型

概要：左係数の反対圏と二つの単体方向の反転で、元の重み付き始域を照合する。
方針：元の二方向要素圏の厳密な往復と元の nerve 反対同型を各次数で使う。
規約：係数と底の両方向を反転し、元の全射列を保持する。
使われ方：既存の一方向 Thomason 定理を元の左比較へ戻す。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource
open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.SimplicialModel

variable {W : Type u} [Category.{u} W]

def elementsNerveIso (A : Wᵒᵖ ⥤ Type u) (S : W ⥤ Type u) :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S) ≅
      (nerve (((Functor.Elements.π S).op ⋙ A).Elements)).op :=
  (show nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S) ≅
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.oppositeElements A S) from
    { hom := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toOpposite A S)
      inv := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromOpposite A S)
      hom_inv_id := by ext n e; rfl
      inv_hom_id := by ext n e; rfl }) ≪≫
    SerrePositivity.KST.ProExcision.nerveOppositeIso _

def oppositeRowsIso (A : Wᵒᵖ ⥤ SSet.{u}) (S : W ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows A (S ⋙ Functor.const SimplexCategoryᵒᵖ) ≅
      (BarConstruction.rows S.Elementsᵒᵖ).obj ((Functor.Elements.π S).op ⋙ A) ⋙ SSet.opFunctor :=
  NatIso.ofComponents (fun n => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.elementsNerveIso (A.flip.obj n) S) (by
    intro n m θ
    ext k e
    rfl)

def outerOpRowsIso (A : Wᵒᵖ ⥤ SSet.{u}) (S : W ⥤ Type u) :
    SimplicialObject.opFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows A (S ⋙ Functor.const SimplexCategoryᵒᵖ)) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows (A ⋙ SSet.opFunctor) (S ⋙ Functor.const SimplexCategoryᵒᵖ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    ext k e
    rfl)

def coefficientRowsIso {A B : Wᵒᵖ ⥤ SSet.{u}} (e : A ≅ B) (S : W ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows A (S ⋙ Functor.const SimplexCategoryᵒᵖ) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows B (S ⋙ Functor.const SimplexCategoryᵒᵖ) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap e.hom (𝟙 _)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap e.inv (𝟙 _)
  hom_inv_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap_comp, e.hom_inv_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap_id]
  inv_hom_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap_comp, e.inv_hom_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap_id]

def nerveOpIso (F : Wᵒᵖ ⥤ Cat.{u, u}) :
    (F ⋙ Cat.opFunctor) ⋙ nerveFunctor ≅ (F ⋙ nerveFunctor) ⋙ SSet.opFunctor :=
  NatIso.ofComponents (fun w => SerrePositivity.KST.ProExcision.nerveOppositeIso (F.obj w)) (by
    intro w w' h
    exact SerrePositivity.KST.ProExcision.nerveOppositeIso_natural _ (F.map h).toFunctor)

def rowsIso (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u) :
    SimplicialObject.opFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows (F ⋙ nerveFunctor) (S ⋙ Functor.const SimplexCategoryᵒᵖ)) ≅
      (BarConstruction.rows S.Elementsᵒᵖ).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S ⋙ nerveFunctor) ⋙ SSet.opFunctor :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.outerOpRowsIso (F ⋙ nerveFunctor) S ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.coefficientRowsIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.nerveOpIso F).symm S ≪≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.oppositeRowsIso ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor) S

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource
