module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation

/-! # The same relative bar as the bar on its actual base comma category

Only the order of recording a comma arrow and its element label changes.
The two actual simplicial maps are inverse, retaining every chain and label.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v}) (b : B)

abbrev commaValues : CostructuredArrow p b ⥤ SSet.{v} := CostructuredArrow.proj p b ⋙ F
abbrev commaBar : SSet.{max uD vD v vB} :=
  (BarConstruction.functor (CostructuredArrow p b)).obj (commaValues p F b)

def commaElements (n : SimplexCategoryᵒᵖ) :
    ((commaValues p F b).flip.obj n).Elements ⥤
      CostructuredArrow (elementProjection p F n) b where
  obj e := CostructuredArrow.mk (Y := (F.flip.obj n).elementsMk e.obj.left e.val) e.obj.hom
  map f := CostructuredArrow.homMk
    (Functor.Elements.homMk f.hom.left f.map_val) (CostructuredArrow.w f.hom)

def elementsComma (n : SimplexCategoryᵒᵖ) :
    CostructuredArrow (elementProjection p F n) b ⥤
      ((commaValues p F b).flip.obj n).Elements where
  obj e := ((commaValues p F b).flip.obj n).elementsMk
    (CostructuredArrow.mk (Y := e.left.obj) e.hom) e.left.val
  map f := Functor.Elements.homMk
    (CostructuredArrow.homMk f.left.hom (CostructuredArrow.w f)) f.left.map_val

def commaBarToRelative : commaBar p F b ⟶ (relative p F).obj b where
  app n := ↾fun c => c ⋙ commaElements p F b n
  naturality {_ _} _ := rfl

def relativeToCommaBar : (relative p F).obj b ⟶ commaBar p F b where
  app n := ↾fun c => c ⋙ elementsComma p F b n
  naturality {_ _} _ := rfl

def commaPresentation : commaBar p F b ≅ (relative p F).obj b where
  hom := commaBarToRelative p F b
  inv := relativeToCommaBar p F b
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro c
    apply CategoryTheory.Functor.ext (fun _ => rfl)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro c
    apply CategoryTheory.Functor.ext (fun _ => rfl)

def totalNerveAugmentation : nerve (TotalNerve.Total (commaValues p F b)) ⟶
    (relative p F).obj b :=
  TotalNerve.augmentation (commaValues p F b) ≫ (commaPresentation p F b).hom

end SerrePositivity.SimplicialModel.BarConstruction
