module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace

/-! # Gluing whole cotensor families along standard simplicial boundaries

Transposition exchanges the external family parameter and the boundary
parameter. Thus the actual subcomplex gluing theorem applies without
assuming a tensor colimit comparison or replacing the boundary object.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BoundaryCotensor
variable {T K P : SSet.{v}}

/-- Exchange the two actual parameters using symmetry and the closed adjunction. -/
def transpose (f : T ⟶ (ihom K).obj P) : K ⟶ (ihom T).obj P :=
  curry ((β_ T K).hom ≫ uncurry f)

lemma transpose_transpose (f : T ⟶ (ihom K).obj P) : transpose (transpose f) = f := by
  apply uncurry_injective
  simp only [transpose, uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry,
    Category.id_comp]

lemma transpose_injective : Function.Injective (transpose (T := T) (K := K) (P := P)) := by
  intro f g h
  simpa only [transpose_transpose] using congrArg transpose h

lemma transpose_restriction {A : SSet.{v}} (i : A ⟶ K) (f : T ⟶ (ihom K).obj P) :
    transpose (f ≫ (pre i).app P) = i ≫ transpose f := by
  apply uncurry_injective
  rw [transpose, uncurry_curry, uncurry_pre_app, uncurry_natural_left,
    transpose, uncurry_curry, ← Category.assoc, ← BraidedCategory.braiding_naturality_right]
  simp only [Category.assoc]

abbrev Compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    faces j ≫ (pre (SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))).app P =
      faces k ≫ (pre (SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)))).app P

lemma transpose_compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) : BoundaryGluing.StandardCompatible (fun k => transpose (faces k)) := by
  intro j k hjk
  rw [← transpose_restriction, ← transpose_restriction, hf j k hjk]

/-- Glue all prescribed whole facet families into the actual boundary cotensor. -/
def standardDesc {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) : T ⟶ (ihom (SSet.boundary.{v} (n + 2)).toSSet).obj P :=
  transpose (BoundaryGluing.standardDesc (fun k => transpose (faces k))
    (transpose_compatible faces hf))

@[reassoc]
lemma standardDesc_fac {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) (k : Fin (n + 3)) :
    standardDesc faces hf ≫ (pre (SSet.boundary.ι k)).app P = faces k := by
  apply transpose_injective
  rw [transpose_restriction, standardDesc, transpose_transpose,
    BoundaryGluing.standardDesc_fac]

lemma hom_ext {n : ℕ} {f g : T ⟶ (ihom (SSet.boundary.{v} (n + 1)).toSSet).obj P}
    (h : ∀ k : Fin (n + 2), f ≫ (pre (SSet.boundary.ι k)).app P =
      g ≫ (pre (SSet.boundary.ι k)).app P) : f = g := by
  apply transpose_injective
  apply SSet.boundary.hom_ext
  intro k
  rw [← transpose_restriction, ← transpose_restriction, h k]

end SerrePositivity.SimplicialModel.BoundaryCotensor
