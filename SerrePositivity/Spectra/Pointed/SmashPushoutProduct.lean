module

public import SerrePositivity.Spectra.Pointed.Smash
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Comparing the product and smash pushout-products

The comparison is constructed in the actual pointed category. It is a
pushout because compatibility with the two boundary arms forces both axes of
the product map to vanish.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.PointedObject
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteColimits C]
  {A B X Y : PointedObject C} (f : A ⟶ B) (g : X ⟶ Y)

abbrev productBoundary := pushout (prodMap f (𝟙 X)) (prodMap (𝟙 A) g)
abbrev smashBoundary := pushout (smashMap f (𝟙 X)) (smashMap (𝟙 A) g)

abbrev productBoundaryInl : prod B X ⟶ productBoundary f g := pushout.inl _ _
abbrev productBoundaryInr : prod A Y ⟶ productBoundary f g := pushout.inr _ _

lemma productBoundary_isPushout :
    IsPushout (prodMap f (𝟙 X)) (prodMap (𝟙 A) g)
      (productBoundaryInl f g) (productBoundaryInr f g) := IsPushout.of_hasPushout _ _

abbrev smashBoundaryInl : smash B X ⟶ smashBoundary f g := pushout.inl _ _
abbrev smashBoundaryInr : smash A Y ⟶ smashBoundary f g := pushout.inr _ _

lemma smashBoundary_isPushout :
    IsPushout (smashMap f (𝟙 X)) (smashMap (𝟙 A) g)
      (smashBoundaryInl f g) (smashBoundaryInr f g) := IsPushout.of_hasPushout _ _

def productPushoutProduct : productBoundary f g ⟶ prod B Y :=
  pushout.desc (prodMap (𝟙 B) g) (prodMap f (𝟙 Y)) (by simp)

@[reassoc (attr := simp)] lemma productBoundaryInl_productPushoutProduct :
    productBoundaryInl f g ≫ productPushoutProduct f g = prodMap (𝟙 B) g := pushout.inl_desc ..

@[reassoc (attr := simp)] lemma productBoundaryInr_productPushoutProduct :
    productBoundaryInr f g ≫ productPushoutProduct f g = prodMap f (𝟙 Y) := pushout.inr_desc ..

def smashPushoutProduct : smashBoundary f g ⟶ smash B Y :=
  pushout.desc (smashMap (𝟙 B) g) (smashMap f (𝟙 Y)) (by simp)

@[reassoc (attr := simp)] lemma smashBoundaryInl_smashPushoutProduct :
    smashBoundaryInl f g ≫ smashPushoutProduct f g = smashMap (𝟙 B) g := pushout.inl_desc ..

@[reassoc (attr := simp)] lemma smashBoundaryInr_smashPushoutProduct :
    smashBoundaryInr f g ≫ smashPushoutProduct f g = smashMap f (𝟙 Y) := pushout.inr_desc ..

/-- Quotient each arm of the product boundary to the smash boundary. -/
def boundaryQuotient : productBoundary f g ⟶ smashBoundary f g :=
  pushout.desc
    (smashQuotient B X ≫ pushout.inl _ _)
    (smashQuotient A Y ≫ pushout.inr _ _) (by
      rw [← smashQuotient_map_assoc, ← smashQuotient_map_assoc, pushout.condition])

@[reassoc (attr := simp)]
lemma boundaryQuotient_inl :
    (pushout.inl _ _ : prod B X ⟶ productBoundary f g) ≫ boundaryQuotient f g =
      smashQuotient B X ≫ pushout.inl _ _ := pushout.inl_desc ..

@[reassoc (attr := simp)]
lemma boundaryQuotient_inr :
    (pushout.inr _ _ : prod A Y ⟶ productBoundary f g) ≫ boundaryQuotient f g =
      smashQuotient A Y ≫ pushout.inr _ _ := pushout.inr_desc ..

lemma boundaryQuotient_comm :
    boundaryQuotient f g ≫ smashPushoutProduct f g =
      productPushoutProduct f g ≫ smashQuotient B Y := by
  apply pushout.hom_ext <;>
    simp [productPushoutProduct, smashPushoutProduct]

/-- A compatible product map kills the first axis, using the B×X boundary arm. -/
lemma boundaryCompatible_axisLeft {W : PointedObject C}
    (u : prod B Y ⟶ W) (v : smashBoundary f g ⟶ W)
    (h : boundaryQuotient f g ≫ v = productPushoutProduct f g ≫ u) :
    axisLeft B Y ≫ u = 0 := by
  have hh := congrArg (fun k ↦ axisLeft B X ≫ 
    (pushout.inl _ _ : prod B X ⟶ productBoundary f g) ≫ k) h
  simpa [productPushoutProduct, Category.assoc] using hh.symm

/-- A compatible product map kills the second axis, using the A×Y boundary arm. -/
lemma boundaryCompatible_axisRight {W : PointedObject C}
    (u : prod B Y ⟶ W) (v : smashBoundary f g ⟶ W)
    (h : boundaryQuotient f g ≫ v = productPushoutProduct f g ≫ u) :
    axisRight B Y ≫ u = 0 := by
  have hh := congrArg (fun k ↦ axisRight A Y ≫ 
    (pushout.inr _ _ : prod A Y ⟶ productBoundary f g) ≫ k) h
  simpa [productPushoutProduct, Category.assoc] using hh.symm

/-- The universal extension through the smash quotient. -/
def boundaryCompatibleDesc {W : PointedObject C}
    (u : prod B Y ⟶ W) (v : smashBoundary f g ⟶ W)
    (h : boundaryQuotient f g ≫ v = productPushoutProduct f g ≫ u) : smash B Y ⟶ W :=
  smashDesc u (boundaryCompatible_axisLeft f g u v h) (boundaryCompatible_axisRight f g u v h)

@[reassoc (attr := simp)]
lemma boundaryCompatibleDesc_quotient {W : PointedObject C}
    (u : prod B Y ⟶ W) (v : smashBoundary f g ⟶ W) (h) :
    smashQuotient B Y ≫ boundaryCompatibleDesc f g u v h = u := smashQuotient_desc ..

lemma boundaryCompatibleDesc_boundary {W : PointedObject C}
    (u : prod B Y ⟶ W) (v : smashBoundary f g ⟶ W) (h) :
    smashPushoutProduct f g ≫ boundaryCompatibleDesc f g u v h = v := by
  apply pushout.hom_ext
  · apply (cancel_epi (smashQuotient B X)).1
    have hh := congrArg (fun k ↦ 
    (pushout.inl _ _ : prod B X ⟶ productBoundary f g) ≫ k) h
    simpa [productPushoutProduct, smashPushoutProduct, Category.assoc] using hh.symm
  · apply (cancel_epi (smashQuotient A Y)).1
    have hh := congrArg (fun k ↦ 
    (pushout.inr _ _ : prod A Y ⟶ productBoundary f g) ≫ k) h
    simpa [productPushoutProduct, smashPushoutProduct, Category.assoc] using hh.symm

/-- The smash pushout-product is the cobase change of the product pushout-product. -/
lemma smashPushoutProduct_isPushout :
    IsPushout (boundaryQuotient f g) (productPushoutProduct f g)
      (smashPushoutProduct f g) (smashQuotient B Y) := by
  apply IsPushout.mk' (boundaryQuotient_comm f g)
  · intro W φ φ' _ hq
    exact smash_hom_ext φ φ' hq
  · intro W v u h
    exact ⟨boundaryCompatibleDesc f g u v h,
      boundaryCompatibleDesc_boundary f g u v h,
      boundaryCompatibleDesc_quotient f g u v h⟩

end SerrePositivity.PointedObject
