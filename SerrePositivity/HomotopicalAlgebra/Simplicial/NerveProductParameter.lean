module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCylinderBoundary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws

/-! # Supplementary constant parameters in whole moving coherent systems -/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.NerveProductParameter
open NerveCylinderBoundary NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{w}) (T : SSet.{w})

def projection : product K T ⟶ K where
  app d := fst (K.obj d) T
  naturality {_ _} f := whiskerRight_fst (K.map f) T

lemma projection_horizontal (V : D ⥤ SSet.{w}) (i : V ⟶ K) :
    horizontal V K i T ≫ projection K T = projection V T ≫ i := by
  apply NatTrans.ext
  funext d
  exact whiskerRight_fst (i.app d) T

lemma projection_vertical {A : SSet.{w}} (j : A ⟶ T) :
    vertical j K ≫ projection K T = projection K A := by
  apply NatTrans.ext
  funext d
  exact whiskerLeft_fst (K.obj d) j

/-- Retain the whole original system, constant in the supplementary parameter. -/
def expand (a : NerveBiparameter.System K F) : NerveBiparameter.System (product K T) F :=
  restrict (product K T) K F (projection K T) a

lemma expand_vertical {A : SSet.{w}} (j : A ⟶ T) (a : NerveBiparameter.System K F) :
    expand K F T a ≫ restriction (product K A) (product K T) F (vertical j K) =
      expand K F A a := by
  change (a ≫ restriction _ _ _ _) ≫ _ = _
  rw [Category.assoc, restriction_comp, projection_vertical]
  rfl

lemma expand_horizontal (V : D ⥤ SSet.{w}) (i : V ⟶ K)
    (a : NerveBiparameter.System K F) : expand K F T a ≫
    restriction (product V T) (product K T) F (horizontal V K i T) =
      expand V F T (a ≫ restriction V K F i) := by
  change (a ≫ restriction _ _ _ _) ≫ _ = (a ≫ _) ≫ _
  rw [Category.assoc, restriction_comp, projection_horizontal,
    Category.assoc, restriction_comp]

lemma expand_natural (b : K ⟶ F) : expand K F T (NerveNaturalBoundary.ofNatTrans K F b) =
    NerveNaturalBoundary.ofNatTrans (product K T) F (projection K T ≫ b) :=
  restrict_natural _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveProductParameter
