module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpan
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftHomotopy

/-! # The actual left leg of the natural comparison span is a simplicial homotopy retract -/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

lemma spanLeft_section_factor (d : D) :
    (spanLeft p F).app d ≫ spanSection p F d =
      SSet.uliftFunctor.{vB, max uD vD v}.map
        ((identityAugmentation F).app d ≫ identitySection F d) := by
  let U := SSet.uliftFunctor.{vB, max uD vD v}
  let e := UniverseLift.iterationIso.{v, max uD vD, vB}.app (F.obj d)
  change (U.map ((identityAugmentation F).app d) ≫ e.hom) ≫
    (e.inv ≫ U.map (identitySection F d)) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← U.map_comp]

/-- The full diagonal contraction survives the actual lift and wrapper-flattening maps. -/
def spanLeftHomotopy (d : D) : SSet.Homotopy (𝟙 ((spanMiddle p F).obj d))
    ((spanLeft p F).app d ≫ spanSection p F d) := by
  have H := UniverseLift.homotopy.{vB} (identityDiagonalHomotopy F d)
  change SSet.Homotopy
    (SSet.uliftFunctor.{vB, max uD vD v}.map (𝟙 ((relative (𝟭 D) F).obj d)))
    (SSet.uliftFunctor.{vB, max uD vD v}.map
      ((identityAugmentation F).app d ≫ identitySection F d)) at H
  rw [CategoryTheory.Functor.map_id, ← spanLeft_section_factor p F d] at H
  exact H

end SerrePositivity.SimplicialModel.BarConstruction
