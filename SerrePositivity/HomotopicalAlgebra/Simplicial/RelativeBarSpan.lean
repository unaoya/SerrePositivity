module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarIdentity
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftIteration

/-! # The natural comparison span through an identity-projection bar

The left map has an explicit pointwise section. The section is not claimed
to be natural in the base. Neither leg is assumed to be a weak equivalence.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev spanMiddle (_p : D ⥤ B) (F : D ⥤ SSet.{v}) : D ⥤ SSet.{max uD vD v vB} :=
  relative (𝟭 D) F ⋙ SSet.uliftFunctor.{vB, max uD vD v}

/-- The actual augmentation, with the two lift wrappers flattened naturally. -/
def spanLeft : spanMiddle p F ⟶ F ⋙ SSet.uliftFunctor.{max uD vD vB, v} :=
  Functor.whiskerRight (identityAugmentation F) SSet.uliftFunctor.{vB, max uD vD v} ≫
    (Functor.isoWhiskerLeft F (UniverseLift.iterationIso.{v, max uD vD, vB})).hom

abbrev spanRight : spanMiddle p F ⟶ p ⋙ relative p F := unit p F

/-- A section at a fixed object, transported through the explicit flattening isomorphism. -/
def spanSection (d : D) : (SSet.uliftFunctor.{max uD vD vB, v}).obj (F.obj d) ⟶
    (spanMiddle p F).obj d :=
  (UniverseLift.iterationIso.{v, max uD vD, vB}.app (F.obj d)).inv ≫
    SSet.uliftFunctor.{vB, max uD vD v}.map (identitySection F d)

lemma spanSection_retract (d : D) :
    spanSection p F d ≫ (spanLeft p F).app d = 𝟙 _ := by
  let U := SSet.uliftFunctor.{vB, max uD vD v}
  let e := UniverseLift.iterationIso.{v, max uD vD, vB}.app (F.obj d)
  change (e.inv ≫ U.map (identitySection F d)) ≫
    (U.map ((identityAugmentation F).app d) ≫ e.hom) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (U.map (identitySection F d)), ← U.map_comp,
    identitySection_retract, U.map_id, Category.id_comp, e.inv_hom_id]

end SerrePositivity.SimplicialModel.BarConstruction
