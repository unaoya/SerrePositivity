module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-! # Whole boundary families with an additional moving tensor parameter

Exchange the external and boundary parameters by the closed adjunction, retaining
an arbitrary additional parameter. Gluing uses the actual simplicial boundary.
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ProductBoundaryCotensor
variable {T K A P : SSet.{w}}

/-- Move the boundary parameter to the source while retaining the moving parameter. -/
def rotate (f : T ⟶ (ihom (K ⊗ A)).obj P) : A ⟶ (ihom K).obj ((ihom T).obj P) :=
  curry (BoundaryCotensor.transpose f)

def unrotate (f : A ⟶ (ihom K).obj ((ihom T).obj P)) : T ⟶ (ihom (K ⊗ A)).obj P :=
  BoundaryCotensor.transpose (uncurry f)

lemma rotate_unrotate (f : A ⟶ (ihom K).obj ((ihom T).obj P)) :
    rotate (unrotate f) = f := by
  rw [rotate, unrotate, BoundaryCotensor.transpose_transpose, curry_uncurry]

lemma unrotate_rotate (f : T ⟶ (ihom (K ⊗ A)).obj P) : unrotate (rotate f) = f := by
  rw [unrotate, rotate, uncurry_curry, BoundaryCotensor.transpose_transpose]

lemma rotate_injective : Function.Injective (rotate (T := T) (K := K) (A := A) (P := P)) := by
  intro f g h
  simpa only [unrotate_rotate] using congrArg unrotate h

lemma rotate_restriction {B : SSet.{w}} (i : B ⟶ A) (f : T ⟶ (ihom (K ⊗ A)).obj P) :
    rotate (f ≫ (pre (K ◁ i)).app P) = i ≫ rotate f := by
  rw [rotate, BoundaryCotensor.transpose_restriction, curry_natural_left]
  rfl

abbrev Compatible {n : ℕ} (faces : Fin (n + 3) →
    (T ⟶ (ihom (K ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    faces j ≫ (pre (K ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))).app P =
      faces k ≫ (pre (K ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)))).app P

lemma rotate_compatible {n : ℕ} (faces : Fin (n + 3) →
    (T ⟶ (ihom (K ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) : BoundaryGluing.StandardCompatible (fun k => rotate (faces k)) := by
  intro j k hjk
  rw [← rotate_restriction, ← rotate_restriction, hf j k hjk]

/-- Glue every prescribed whole facet, with no model structure or tensor colimit hypothesis. -/
def standardDesc {n : ℕ} (faces : Fin (n + 3) →
    (T ⟶ (ihom (K ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) : T ⟶ (ihom (K ⊗ (SSet.boundary (n + 2)).toSSet)).obj P :=
  unrotate (BoundaryGluing.standardDesc (fun k => rotate (faces k)) (rotate_compatible faces hf))

@[reassoc]
lemma standardDesc_fac {n : ℕ} (faces : Fin (n + 3) →
    (T ⟶ (ihom (K ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) (k : Fin (n + 3)) :
    standardDesc faces hf ≫ (pre (K ◁ SSet.boundary.ι k)).app P = faces k := by
  apply rotate_injective
  rw [rotate_restriction, standardDesc, rotate_unrotate, BoundaryGluing.standardDesc_fac]

lemma hom_ext {n : ℕ}
    {f g : T ⟶ (ihom (K ⊗ (SSet.boundary (n + 1)).toSSet)).obj P}
    (h : ∀ k : Fin (n + 2), f ≫ (pre (K ◁ SSet.boundary.ι k)).app P =
      g ≫ (pre (K ◁ SSet.boundary.ι k)).app P) : f = g := by
  apply rotate_injective
  apply SSet.boundary.hom_ext
  intro k
  rw [← rotate_restriction, ← rotate_restriction, h k]

lemma parameter_hom_ext {n : ℕ} {f g : K ⊗ (SSet.boundary (n + 1)).toSSet ⟶ P}
    (h : ∀ k : Fin (n + 2), K ◁ SSet.boundary.ι k ≫ f = K ◁ SSet.boundary.ι k ≫ g) :
    f = g := by
  apply curry_injective
  apply SSet.boundary.hom_ext
  intro k
  rw [← curry_natural_left, ← curry_natural_left, h k]

end SerrePositivity.SimplicialModel.ProductBoundaryCotensor
