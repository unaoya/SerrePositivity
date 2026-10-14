module

public import SerrePositivity.HomotopicalAlgebra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.SmashPushoutProduct
public import Mathlib.CategoryTheory.Limits.Comma

/-! # Pushout-product compatibility of the existing pointed smash

The product boundary is evaluated to a pushout-product in C. The smash
pushout-product is its cobase change in the pointed model category.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
namespace SerrePositivity.PointedModel
open SerrePositivity.PointedObject SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [ModelCategory C]
  {A B X Y : PointedObject C} (f : A ⟶ B) (g : X ⟶ Y)

/-- Forgetting the product boundary gives a genuine base-category pushout-product. -/
def underlyingProductSquare : (curriedTensor C).PushoutObjObj f.right g.right where
  pt := (productBoundary f g).right
  inl := (productBoundaryInl f g).right
  inr := (productBoundaryInr f g).right
  isPushout := by
    have h := (productBoundary_isPushout f g).map (forget (C := C))
    change IsPushout (f.right ▷ X.right) (A.right ◁ g.right) _ _
    change IsPushout (prodMap f (𝟙 X)).right (prodMap (𝟙 A) g).right
      (productBoundaryInl f g).right (productBoundaryInr f g).right at h
    simpa only [prodMap_right, Under.id_right, tensorHom_id, id_tensorHom] using h
  ι := (productPushoutProduct f g).right
  inl_ι := by
    change ((productBoundaryInl f g) ≫
      productPushoutProduct f g).right = B.right ◁ g.right
    simp only [productBoundaryInl_productPushoutProduct, prodMap_right,
      Under.id_right, id_tensorHom]
  inr_ι := by
    change ((productBoundaryInr f g) ≫
      productPushoutProduct f g).right = f.right ▷ Y.right
    simp only [productBoundaryInr_productPushoutProduct, prodMap_right,
      Under.id_right, tensorHom_id]

variable [IsQuillenBifunctor (curriedTensor C)]

lemma productPushoutProduct_cofibration [Cofibration f] [Cofibration g] :
    Cofibration (productPushoutProduct f g) := by
  apply (cofibration_iff_underlying _).2
  exact IsQuillenBifunctor.cofibration f.right g.right (underlyingProductSquare f g)
    inferInstance inferInstance

lemma smashPushoutProduct_cofibration [Cofibration f] [Cofibration g] :
    Cofibration (smashPushoutProduct f g) := by
  have := productPushoutProduct_cofibration f g
  exact (cofibration_iff _).2 ((cofibrations (PointedObject C)).of_isPushout
    (smashPushoutProduct_isPushout f g) (mem_cofibrations _))

lemma smashPushoutProduct_weakEquivalence [Cofibration f] [Cofibration g]
    (h : WeakEquivalence f ∨ WeakEquivalence g) : WeakEquivalence (smashPushoutProduct f g) := by
  have := productPushoutProduct_cofibration f g
  have hw : WeakEquivalence (productPushoutProduct f g) := by
    apply (weakEquivalence_iff_underlying _).2
    apply IsQuillenBifunctor.weakEquivalence f.right g.right (underlyingProductSquare f g)
      inferInstance inferInstance
    exact h.imp ((weakEquivalence_iff_underlying f).1) ((weakEquivalence_iff_underlying g).1)
  have := hw
  exact (weakEquivalence_iff _).2
    (((trivialCofibrations (PointedObject C)).of_isPushout
      (smashPushoutProduct_isPushout f g) (mem_trivialCofibrations _)).2)

variable [MonoidalClosed C]

/-- Use the already chosen smash boundary as a Mathlib pushout-product square. -/
def smashSquare : (curriedTensor (PointedObject C)).PushoutObjObj f g where
  pt := smashBoundary f g
  inl := smashBoundaryInl f g
  inr := smashBoundaryInr f g
  isPushout := smashBoundary_isPushout f g
  ι := smashPushoutProduct f g
  inl_ι := smashBoundaryInl_smashPushoutProduct f g
  inr_ι := smashBoundaryInr_smashPushoutProduct f g

/-- The existing smash satisfies the two-variable Quillen conditions for every
choice of pushout square. -/
lemma smash_isQuillenBifunctor : IsQuillenBifunctor (curriedTensor (PointedObject C)) := by
  constructor
  · intro A B X Y i j sq hi hj
    have := hi
    have := hj
    have hc := smashPushoutProduct_cofibration i j
    have e := Functor.PushoutObjObj.ι_iso_of_iso_left
      (F := curriedTensor (PointedObject C)) (f₂ := Arrow.mk j) (smashSquare i j) sq
      (Iso.refl (Arrow.mk i))
    exact (cofibration_iff sq.ι).2
      (((cofibrations (PointedObject C)).arrow_mk_iso_iff e).1
        ((cofibration_iff (smashPushoutProduct i j)).1 hc))
  · intro A B X Y i j sq hi hj hw
    have := hi
    have := hj
    have hc := smashPushoutProduct_weakEquivalence i j hw
    have e := Functor.PushoutObjObj.ι_iso_of_iso_left
      (F := curriedTensor (PointedObject C)) (f₂ := Arrow.mk j) (smashSquare i j) sq
      (Iso.refl (Arrow.mk i))
    exact (weakEquivalence_iff sq.ι).2
      (((weakEquivalences (PointedObject C)).arrow_mk_iso_iff e).1
        ((weakEquivalence_iff (smashPushoutProduct i j)).1 hc))

/-- Cartesian monoidal model compatibility induces compatibility for the actual smash. -/
lemma smash_monoidalModel [IsCofibrant (𝟙_ C)] : MonoidalModelCategory (PointedObject C) :=
  ⟨smash_isQuillenBifunctor, smash_hasUnitAxiom⟩

/-- The closed pointed pullback-Hom criterion (SM7) for the actual internal Hom. -/
lemma smash_hasQuillenPullbackHom :
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := PointedObject C)) :=
  (isQuillenBifunctor_iff_pullbackHom
    (MonoidalClosed.internalHomAdjunction₂ (C := PointedObject C))).1 smash_isQuillenBifunctor

end SerrePositivity.PointedModel
