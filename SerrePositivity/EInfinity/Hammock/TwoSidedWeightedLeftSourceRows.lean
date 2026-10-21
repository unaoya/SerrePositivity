module

public import SerrePositivity.EInfinity.Hammock.TwoSidedElementsOpposite
public import SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftMap
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
namespace SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftSource
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel

variable {W : Type u} [Category.{u} W]

def elementsNerveIso (A : Wᵒᵖ ⥤ Type u) (S : W ⥤ Type u) :
    nerve (TwoSidedElements.Element A S) ≅
      (nerve (((Functor.Elements.π S).op ⋙ A).Elements)).op :=
  (show nerve (TwoSidedElements.Element A S) ≅
      nerve (TwoSidedElements.oppositeElements A S) from
    { hom := nerveMap (TwoSidedElements.toOpposite A S)
      inv := nerveMap (TwoSidedElements.fromOpposite A S)
      hom_inv_id := by ext n e; rfl
      inv_hom_id := by ext n e; rfl }) ≪≫
    SerrePositivity.KST.ProExcision.nerveOppositeIso _

def oppositeRowsIso (A : Wᵒᵖ ⥤ SSet.{u}) (S : W ⥤ Type u) :
    TwoSidedBar.rows A (S ⋙ Functor.const SimplexCategoryᵒᵖ) ≅
      (BarConstruction.rows S.Elementsᵒᵖ).obj ((Functor.Elements.π S).op ⋙ A) ⋙ SSet.opFunctor :=
  NatIso.ofComponents (fun n => elementsNerveIso (A.flip.obj n) S) (by
    intro n m θ
    ext k e
    rfl)

def outerOpRowsIso (A : Wᵒᵖ ⥤ SSet.{u}) (S : W ⥤ Type u) :
    SimplicialObject.opFunctor.obj (TwoSidedBar.rows A (S ⋙ Functor.const SimplexCategoryᵒᵖ)) ≅
      TwoSidedBar.rows (A ⋙ SSet.opFunctor) (S ⋙ Functor.const SimplexCategoryᵒᵖ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    ext k e
    rfl)

def coefficientRowsIso {A B : Wᵒᵖ ⥤ SSet.{u}} (e : A ≅ B) (S : W ⥤ Type u) :
    TwoSidedBar.rows A (S ⋙ Functor.const SimplexCategoryᵒᵖ) ≅
      TwoSidedBar.rows B (S ⋙ Functor.const SimplexCategoryᵒᵖ) where
  hom := TwoSidedBar.rowMap e.hom (𝟙 _)
  inv := TwoSidedBar.rowMap e.inv (𝟙 _)
  hom_inv_id := by
    rw [← TwoSidedBar.rowMap_comp, e.hom_inv_id, Category.id_comp, TwoSidedBar.rowMap_id]
  inv_hom_id := by
    rw [← TwoSidedBar.rowMap_comp, e.inv_hom_id, Category.id_comp, TwoSidedBar.rowMap_id]

def nerveOpIso (F : Wᵒᵖ ⥤ Cat.{u, u}) :
    (F ⋙ Cat.opFunctor) ⋙ nerveFunctor ≅ (F ⋙ nerveFunctor) ⋙ SSet.opFunctor :=
  NatIso.ofComponents (fun w => SerrePositivity.KST.ProExcision.nerveOppositeIso (F.obj w)) (by
    intro w w' h
    exact SerrePositivity.KST.ProExcision.nerveOppositeIso_natural _ (F.map h).toFunctor)

def rowsIso (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u) :
    SimplicialObject.opFunctor.obj
      (TwoSidedBar.rows (F ⋙ nerveFunctor) (S ⋙ Functor.const SimplexCategoryᵒᵖ)) ≅
      (BarConstruction.rows S.Elementsᵒᵖ).obj
        (TwoSidedMixedLabel.pulledDiagram F S ⋙ nerveFunctor) ⋙ SSet.opFunctor :=
  outerOpRowsIso (F ⋙ nerveFunctor) S ≪≫
    coefficientRowsIso (nerveOpIso F).symm S ≪≫
      oppositeRowsIso ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor) S

end SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftSource
