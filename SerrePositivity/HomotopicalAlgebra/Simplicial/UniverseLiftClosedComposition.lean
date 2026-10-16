module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterComposition

/-! # The actual universe comparison preserves standard closed composition and identity -/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.UniverseLiftClosedComposition

lemma composition (K P Q : SSet.{v}) :
    ((UniverseLiftParameterHom.closedIso K P).hom ⊗ₘ
      (UniverseLiftParameterHom.closedIso P Q).hom) ≫
        MonoidalClosed.comp (UniverseLift.obj.{w} K) (UniverseLift.obj P) (UniverseLift.obj Q) =
    (UniverseLift.tensorIso.{w} ((ihom K).obj P) ((ihom P).obj Q)).inv ≫
      UniverseLift.map (MonoidalClosed.comp K P Q) ≫
        (UniverseLiftParameterHom.closedIso K Q).hom := by
  rw [MonoidalClosed.comp_eq K P Q, UniverseLiftClosedCurry.curry_tensorMap]
  apply uncurry_injective
  rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    uncurry_natural_left, uncurry_curry, MonoidalClosed.compTranspose_eq]
  ext n x
  have hf := types_congr_hom (congr_app (UniverseLiftClosedCurry.evaluation.{w} K P) n)
    (x.1, x.2.1)
  have hg := types_congr_hom (congr_app (UniverseLiftClosedCurry.evaluation.{w} P Q) n)
    (ULift.up (((ihom.ev K).app P).app n (x.1.down, x.2.1.down)), x.2.2)
  change ((ihom.ev (UniverseLift.obj.{w} K)).app (UniverseLift.obj P)).app n
    (x.1, (UniverseLiftParameterHom.closedIso K P).hom.app n x.2.1) =
      ULift.up (((ihom.ev K).app P).app n (x.1.down, x.2.1.down)) at hf
  change ((ihom.ev (UniverseLift.obj.{w} P)).app (UniverseLift.obj Q)).app n
    (ULift.up (((ihom.ev K).app P).app n (x.1.down, x.2.1.down)),
      (UniverseLiftParameterHom.closedIso P Q).hom.app n x.2.2) =
      ULift.up (((ihom.ev P).app Q).app n
        (((ihom.ev K).app P).app n (x.1.down, x.2.1.down), x.2.2.down)) at hg
  change ((ihom.ev (UniverseLift.obj.{w} P)).app (UniverseLift.obj Q)).app n
    (((ihom.ev (UniverseLift.obj K)).app (UniverseLift.obj P)).app n
      (x.1, (UniverseLiftParameterHom.closedIso K P).hom.app n x.2.1),
        (UniverseLiftParameterHom.closedIso P Q).hom.app n x.2.2) = _
  rw [hf]
  exact hg

lemma identity (K : SSet.{v}) :
    UniverseLift.map.{w} (MonoidalClosed.id K) ≫ (UniverseLiftParameterHom.closedIso K K).hom =
      toUnit (UniverseLift.obj.{w} (𝟙_ SSet.{v})) ≫ MonoidalClosed.id (UniverseLift.obj.{w} K) := by
  rw [MonoidalClosed.id_eq, UniverseLiftClosedCurry.curry_tensorMap]
  have h : UniverseLift.tensorMap.{w} (ρ_ K).hom =
      fst (UniverseLift.obj.{w} K) (UniverseLift.obj.{w} (𝟙_ SSet.{v})) := by
    ext n x
    rfl
  rw [h, ClosedParameterComposition.curry_fst]

def liftedComposition (K P Q : SSet.{v}) :
    UniverseLift.obj.{w} ((ihom K).obj P) ⊗ UniverseLift.obj.{w} ((ihom P).obj Q) ⟶
      UniverseLift.obj.{w} ((ihom K).obj Q) :=
  (UniverseLift.tensorIso.{w} ((ihom K).obj P) ((ihom P).obj Q)).inv ≫
    UniverseLift.map (MonoidalClosed.comp K P Q)

lemma inverse_composition (K P Q : SSet.{v}) :
    ((UniverseLiftParameterHom.closedIso K P).inv ⊗ₘ
      (UniverseLiftParameterHom.closedIso P Q).inv) ≫ liftedComposition.{w} K P Q =
    MonoidalClosed.comp (UniverseLift.obj.{w} K) (UniverseLift.obj P) (UniverseLift.obj Q) ≫
      (UniverseLiftParameterHom.closedIso K Q).inv := by
  apply (cancel_mono (UniverseLiftParameterHom.closedIso K Q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [liftedComposition, Category.assoc, ← composition]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp

def unitParameter (T : SSet.{max w v}) : T ⟶ UniverseLift.obj.{w} (𝟙_ SSet.{v}) where
  app _ := ↾fun _ => ULift.up PUnit.unit
  naturality _ := by
    intro _ _
    rfl

def unitFrom (K : SSet.{v}) (T : SSet.{max w v}) :
    T ⟶ UniverseLift.obj.{w} ((ihom K).obj K) :=
  unitParameter T ≫ UniverseLift.map (MonoidalClosed.id K)

lemma unitFrom_eq (K : SSet.{v}) (T : SSet.{max w v}) :
    unitFrom K T = toUnit T ≫ MonoidalClosed.id (UniverseLift.obj.{w} K) ≫
      (UniverseLiftParameterHom.closedIso K K).inv := by
  apply (cancel_mono (UniverseLiftParameterHom.closedIso K K).hom).mp
  simp only [unitFrom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [identity, ← Category.assoc, comp_toUnit]

end SerrePositivity.SimplicialModel.UniverseLiftClosedComposition
