module

public import SerrePositivity.PerfectComplex.TensorTriple

/-! # Scalar coordinates on selected homogeneous tensor summands -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Select one bidegree and apply its two scalar coordinates. -/
def cochainTensorScalarCoordinate (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ : ℤ) (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (n : ℤ) : (cochainTensor P Q).X n ⟶ ModuleCat.of R R :=
  HomologicalComplex₂.totalDesc _ (fun i j h => by
    by_cases hi : i = i₀
    · subst i
      by_cases hj : j = j₀
      · subst j
        exact (f ⊗ₘ g) ≫ (λ_ (ModuleCat.of R R)).hom
      · exact 0
    · exact 0)

@[reassoc]
lemma ι_cochainTensorScalarCoordinate_match (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ n : ℤ) (h : i₀ + j₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R) :
    ιTensorObj P Q i₀ j₀ n h ≫ cochainTensorScalarCoordinate P Q i₀ j₀ f g n =
      (f ⊗ₘ g) ≫ (λ_ (ModuleCat.of R R)).hom := by
  simp [cochainTensorScalarCoordinate]

@[reassoc]
lemma ι_cochainTensorScalarCoordinate_other (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ i j n : ℤ) (h : i + j = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (hne : i ≠ i₀ ∨ j ≠ j₀) :
    ιTensorObj P Q i j n h ≫ cochainTensorScalarCoordinate P Q i₀ j₀ f g n = 0 := by
  by_cases hi : i = i₀
  · subst i
    have hj : j ≠ j₀ := hne.resolve_left (not_not.mpr rfl)
    simp [cochainTensorScalarCoordinate, hj]
  · simp [cochainTensorScalarCoordinate, hi]

lemma cochainTensorScalarCoordinate_apply_match (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ n : ℤ) (h : i₀ + j₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (x : P.X i₀) (y : Q.X j₀) :
    cochainTensorScalarCoordinate P Q i₀ j₀ f g n (ιTensorObj P Q i₀ j₀ n h (x ⊗ₜ[R] y)) =
      f x * g y :=
  congrArg (fun α => α (x ⊗ₜ[R] y)) (ι_cochainTensorScalarCoordinate_match P Q i₀ j₀ n h f g)

lemma cochainTensorScalarCoordinate_apply_other (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ i j n : ℤ) (h : i + j = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (hne : i ≠ i₀ ∨ j ≠ j₀) (x : P.X i) (y : Q.X j) :
    cochainTensorScalarCoordinate P Q i₀ j₀ f g n (ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) = 0 :=
  congrArg (fun α => α (x ⊗ₜ[R] y))
    (ι_cochainTensorScalarCoordinate_other P Q i₀ j₀ i j n h f g hne)

/-- Select a tridegree and multiply the three scalar coordinates. -/
def cochainTensorTripleScalarCoordinate (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ k₀ : ℤ) (f : P.X i₀ ⟶ ModuleCat.of R R)
    (g : Q.X j₀ ⟶ ModuleCat.of R R) (e : T.X k₀ ⟶ ModuleCat.of R R)
    (n : ℤ) : (cochainTensor (cochainTensor P Q) T).X n ⟶ ModuleCat.of R R :=
  HomologicalComplex₂.totalDesc _ (fun s k h => by
    by_cases hk : k = k₀
    · subst k
      exact (cochainTensorScalarCoordinate P Q i₀ j₀ f g s ⊗ₘ e) ≫
        (λ_ (ModuleCat.of R R)).hom
    · exact 0)

lemma cochainTensorTripleScalarCoordinate_apply_outer_match
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ s n : ℤ) (h : s + k₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (w : (cochainTensor P Q).X s) (z : T.X k₀) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
        (ιTensorObj (cochainTensor P Q) T s k₀ n h (w ⊗ₜ[R] z)) =
      cochainTensorScalarCoordinate P Q i₀ j₀ f g s w * e z := by
  have he : ιTensorObj (cochainTensor P Q) T s k₀ n h ≫
      cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n =
      (cochainTensorScalarCoordinate P Q i₀ j₀ f g s ⊗ₘ e) ≫
        (λ_ (ModuleCat.of R R)).hom := by simp [cochainTensorTripleScalarCoordinate]
  exact congrArg (fun α => α (w ⊗ₜ[R] z)) he

lemma cochainTensorTripleScalarCoordinate_apply_outer_other
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ s k n : ℤ) (h : s + k = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (hk : k ≠ k₀)
    (w : (cochainTensor P Q).X s) (z : T.X k) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
      (ιTensorObj (cochainTensor P Q) T s k n h (w ⊗ₜ[R] z)) = 0 := by
  have he : ιTensorObj (cochainTensor P Q) T s k n h ≫
      cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n = 0 := by
    simp [cochainTensorTripleScalarCoordinate, hk]
  exact congrArg (fun α => α (w ⊗ₜ[R] z)) he

lemma cochainTensorTripleScalarCoordinate_apply_match
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ n : ℤ) (h : i₀ + j₀ + k₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (x : P.X i₀) (y : Q.X j₀) (z : T.X k₀) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
      (cochainTensorTripleι P Q T i₀ j₀ k₀ n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      (f x * g y) * e z := by
  rw [cochainTensorTripleι_apply, cochainTensorTripleScalarCoordinate_apply_outer_match,
    cochainTensorScalarCoordinate_apply_match]

lemma cochainTensorTripleScalarCoordinate_apply_other
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ i j k n : ℤ) (h : i + j + k = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (hne : i ≠ i₀ ∨ j ≠ j₀ ∨ k ≠ k₀)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) = 0 := by
  rw [cochainTensorTripleι_apply]
  by_cases hk : k = k₀
  · subst k
    rw [cochainTensorTripleScalarCoordinate_apply_outer_match,
      cochainTensorScalarCoordinate_apply_other P Q i₀ j₀ i j (i + j) rfl f g (by tauto), zero_mul]
  · exact cochainTensorTripleScalarCoordinate_apply_outer_other P Q T i₀ j₀ k₀ (i + j) k n h
      f g e hk _ z

end SerrePositivity
