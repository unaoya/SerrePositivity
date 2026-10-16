module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterComposition

/-! # Whole endpoint equations survive the actual parameter and value transports -/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.NerveProductEndpointTransport
open NerveBiparameterMaps NerveCylinderBoundary NerveProductParameter
variable {D : Type uD} [Category.{vD} D] (V K F G : D ⥤ SSet.{w})
  (i : V ⟶ K) (p : F ⟶ G)

lemma mapTarget_restrict (a : NerveBiparameter.System K F) :
    mapTarget K F G p a ≫ restriction V K G i = mapTarget V F G p (a ≫ restriction V K F i) := by
  change (a ≫ targetMap _ _ _ _) ≫ _ = (a ≫ _) ≫ _
  rw [Category.assoc, target_restriction, ← Category.assoc]

variable {A T : SSet.{w}} (j : A ⟶ T) (a : NerveBiparameter.System (product K T) F)
  (b : NerveBiparameter.System K F)
  (he : a ≫ restriction (product K A) (product K T) F (vertical j K) = expand K F A b)

include he in
lemma mapTarget_endpoint : mapTarget (product K T) F G p a ≫
    restriction (product K A) (product K T) G (vertical j K) =
      expand K G A (mapTarget K F G p b) := by
  rw [mapTarget_restrict, he, ← expand_mapTarget]

include he in
lemma restrict_endpoint : restrict (product V T) (product K T) F (horizontal V K i T) a ≫
    restriction (product V A) (product V T) F (vertical j V) =
      expand V F A (restrict V K F i b) := by
  change (a ≫ restriction _ _ _ _) ≫ _ = _
  rw [Category.assoc, restriction_comp, ← commute V K i j, ← restriction_comp,
    ← Category.assoc, he]
  exact expand_horizontal K F A V i b

end SerrePositivity.SimplicialModel.NerveProductEndpointTransport
