module
public import SerrePositivity.DifferentialGraded.Quotient.AppendRight
public import SerrePositivity.DifferentialGraded.Quotient.AppendPrepend

/-! # 左有限pathの連結と先頭Hom作用の全右pathに関する結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma appendRight_prepend {S : Set D} (w : Word S) (x y z t : D) :
    (prependMap A D w x y z ▷ internalHom A D S z t) ≫ appendRight A D w x z t =
    (α_ (homObject A D x y) (term A D w y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ appendRight A D w y z t ≫ internalPrepend A D S x y t := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y ⊗ term A D w y z)
    (fun v : Word S => term A D v z t)).hom_ext
  rintro ⟨v⟩
  change ((homObject A D x y ⊗ term A D w y z) ◁ ι A D S z t v) ≫
      (prependMap A D w x y z ▷ internalHom A D S z t) ≫ appendRight A D w x z t =
    ((homObject A D x y ⊗ term A D w y z) ◁ ι A D S z t v) ≫
      (α_ (homObject A D x y) (term A D w y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ appendRight A D w y z t ≫ internalPrepend A D S x y t
  rw [whisker_exchange_assoc, appendRight_ι, appendMap_prepend_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, appendRight_ι,
    whiskerLeft_comp_assoc, internalPrepend_ι]

end SerrePositivity.DifferentialGraded.DGQuotient
