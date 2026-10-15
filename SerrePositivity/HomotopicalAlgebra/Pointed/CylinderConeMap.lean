module

public import SerrePositivity.HomotopicalAlgebra.Pointed.CylinderCone

/-! # Maps of cylinder cones and their quotients

Only compatibility with the two endpoints is needed for the cone map.
Projection compatibility, cofibrancy and good-cylinder conditions are not
assumptions of these categorical naturality laws.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ZeroObject

namespace SerrePositivity.ModelCylinder
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  [HasZeroObject C] [HasZeroMorphisms C] [ModelCategory C]
  {X Y : C} (P : Cylinder X) (R : Cylinder Y)
  (f : X ⟶ Y) (k : P.I ⟶ R.I)
  (h₀ : P.i₀ ≫ k = f ≫ R.i₀) (h₁ : P.i₁ ≫ k = f ≫ R.i₁)

def coneMap : cone P ⟶ cone R :=
  pushout.map P.i₀ (0 : X ⟶ (0 : C)) R.i₀ (0 : Y ⟶ (0 : C))
    k (𝟙 (0 : C)) f h₀ (by simp)

@[reassoc (attr := simp)] lemma coneInclusion_coneMap :
    coneInclusion P ≫ coneMap P R f k h₀ = k ≫ coneInclusion R := pushout.inl_desc ..

include h₁ in
@[reassoc] lemma coneEndpoint_coneMap :
    coneEndpoint P ≫ coneMap P R f k h₀ = f ≫ coneEndpoint R := by
  rw [coneEndpoint, Category.assoc, coneInclusion_coneMap, ← Category.assoc, h₁, Category.assoc]
  rfl

variable {S T : C} (q : P.I ⟶ S) (r : R.I ⟶ T)
  (sq : IsPushout P.i (0 : X ⨿ X ⟶ (0 : C)) q (0 : (0 : C) ⟶ S))
  (sr : IsPushout R.i (0 : Y ⨿ Y ⟶ (0 : C)) r (0 : (0 : C) ⟶ T))
  (z : S ⟶ T) (hz : q ≫ z = k ≫ r)

include hz in
lemma coneQuotient_naturality :
    coneQuotient P q sq ≫ z = coneMap P R f k h₀ ≫ coneQuotient R r sr := by
  apply pushout.hom_ext
  · rw [coneInclusion_coneQuotient_assoc, coneInclusion_coneMap_assoc,
      coneInclusion_coneQuotient, hz]
  · exact (isZero_zero C).eq_of_src _ _

end SerrePositivity.ModelCylinder
