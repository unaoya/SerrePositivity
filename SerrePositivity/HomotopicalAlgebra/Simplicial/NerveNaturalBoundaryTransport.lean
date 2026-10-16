module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport

/-! # Transporting a fixed whole natural boundary through actual parameter squares -/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel
open NerveBiparameterMaps NerveCylinderBoundary NerveProductParameter

namespace SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport
variable {D : Type uD} [Category.{vD} D]
  (V K W L F : D ⥤ SSet.{w}) (i : V ⟶ K) (j : W ⟶ L) (f : K ⟶ L) (g : V ⟶ W)
  (hs : i ≫ f = g ≫ j) (a : NerveBiparameter.System L F) (b : W ⟶ F)
  (hb : a ≫ restriction W L F j = NerveNaturalBoundary.ofNatTrans W F b)

include hs hb in
lemma restrict_square : restrict K L F f a ≫ restriction V K F i =
    NerveNaturalBoundary.ofNatTrans V F (g ≫ b) := by
  change (a ≫ restriction K L F f) ≫ restriction V K F i = _
  rw [Category.assoc, restriction_comp, hs, ← restriction_comp, ← Category.assoc,
    hb, restrict_natural]

include hs in
lemma horizontal_square (T : SSet.{w}) :
    horizontal V K i T ≫ horizontal K L f T = horizontal V W g T ≫ horizontal W L j T := by
  apply NatTrans.ext
  funext d
  change i.app d ▷ T ≫ f.app d ▷ T = g.app d ▷ T ≫ j.app d ▷ T
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  exact congrArg (fun k => k ▷ T) (congr_app hs d)

variable (T : SSet.{w}) (c : NerveBiparameter.System (product L T) F)
  (d : W ⟶ F)
  (hc : c ≫ restriction _ _ F (horizontal W L j T) =
    NerveNaturalBoundary.ofNatTrans _ _ (projection W T ≫ d))

include hs hc in
lemma horizontal_fixed : restrict _ _ F (horizontal K L f T) c ≫
    restriction _ _ F (horizontal V K i T) =
    NerveNaturalBoundary.ofNatTrans _ _ (projection V T ≫ g ≫ d) := by
  apply (restrict_square (product V T) (product K T) (product W T) (product L T) F
    (horizontal V K i T) (horizontal W L j T) (horizontal K L f T) (horizontal V W g T)
    (horizontal_square V K W L i j f g hs T) c (projection W T ≫ d) hc).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  rw [← Category.assoc, projection_horizontal, Category.assoc]

end SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport
