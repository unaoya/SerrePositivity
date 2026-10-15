module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # Inverting the scalar in a scalar-weighted sequential colimit -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u w
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R : Type w} [CommRing R]
variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear R B]
variable [HasColimitsOfShape ℕ B]
variable (a : R) (X : ℕ → B) (t : ∀ n, X n ⟶ X (n + 1))

/-- A sequence whose transition maps carry the specified scalar factor. -/
def scalarWeightedSequence : ℕ ⥤ B := Functor.ofSequence (fun n => a • t n)

/-- The weighted transition is exactly the relation in the actual categorical colimit. -/
lemma scalarWeightedSequence_step (n : ℕ) :
    (a • t n) ≫ colimit.ι (scalarWeightedSequence a X t) (n + 1) =
      colimit.ι (scalarWeightedSequence a X t) n := by
  simpa only [scalarWeightedSequence, Functor.ofSequence_map_homOfLE_succ] using
    (colimit.w (scalarWeightedSequence a X t) (homOfLE (Nat.le_succ n)))

/-- Shifting one stage without its scalar factor gives a compatible inverse cocone. -/
def scalarWeightedColimitInverseCocone : Cocone (scalarWeightedSequence a X t) where
  pt := colimit (scalarWeightedSequence a X t)
  ι := NatTrans.ofSequence
    (fun n => t n ≫ colimit.ι (scalarWeightedSequence a X t) (n + 1)) (by
      intro n
      simp only [scalarWeightedSequence, Functor.ofSequence_map_homOfLE_succ,
        Functor.const_obj_map]
      calc
        (a • t n) ≫ (t (n + 1) ≫ colimit.ι (scalarWeightedSequence a X t) (n + 2)) =
            t n ≫ ((a • t (n + 1)) ≫
              colimit.ι (scalarWeightedSequence a X t) (n + 2)) := by
          simp only [Linear.smul_comp, Linear.comp_smul]
        _ = t n ≫ colimit.ι (scalarWeightedSequence a X t) (n + 1) := by
          rw [scalarWeightedSequence_step]
        _ = _ := (Category.comp_id _).symm)

/-- The actual inverse candidate to multiplication by a on the weighted colimit. -/
def scalarWeightedColimitInverse :
    colimit (scalarWeightedSequence a X t) ⟶ colimit (scalarWeightedSequence a X t) :=
  colimit.desc _ (scalarWeightedColimitInverseCocone a X t)

/-- The inverse is explicitly the unweighted transition followed by the next inclusion. -/
lemma scalarWeightedColimitInverse_ι (n : ℕ) :
    colimit.ι (scalarWeightedSequence a X t) n ≫ scalarWeightedColimitInverse a X t =
      t n ≫ colimit.ι (scalarWeightedSequence a X t) (n + 1) :=
  colimit.ι_desc _ n

/-- Scalar multiplication followed by the constructed inverse is the identity. -/
lemma scalarWeightedColimit_scalar_inverse :
    (a • 𝟙 (colimit (scalarWeightedSequence a X t))) ≫
      scalarWeightedColimitInverse a X t = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  rw [← Category.assoc, Linear.comp_smul, Category.comp_id,
    Linear.smul_comp, scalarWeightedColimitInverse_ι]
  simpa only [Linear.smul_comp] using scalarWeightedSequence_step a X t n

/-- The scalar is invertible on the colimit, including zero scalars and zero objects. -/
def scalarWeightedColimitScalarIso :
    colimit (scalarWeightedSequence a X t) ≅ colimit (scalarWeightedSequence a X t) where
  hom := a • 𝟙 _
  inv := scalarWeightedColimitInverse a X t
  hom_inv_id := scalarWeightedColimit_scalar_inverse a X t
  inv_hom_id := by
    calc
      scalarWeightedColimitInverse a X t ≫ (a • 𝟙 _) =
          (a • 𝟙 _) ≫ scalarWeightedColimitInverse a X t := by
        simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
      _ = _ := scalarWeightedColimit_scalar_inverse a X t

/-- Invertibility is available to arbitrary linear functors and homology functors. -/
instance scalarWeightedColimit_scalar_isIso :
    IsIso (a • 𝟙 (colimit (scalarWeightedSequence a X t))) :=
  (scalarWeightedColimitScalarIso a X t).isIso_hom

end SerrePositivity
