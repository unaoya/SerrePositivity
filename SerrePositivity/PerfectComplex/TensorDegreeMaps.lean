module

public import SerrePositivity.KTheory.Adams.TensorSquare

/-! # Tensor maps of graded components

These maps do not require compatibility with the differentials. They allow
degreewise splittings to be used without treating them as chain splittings.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]
variable {P P' P'' Q Q' Q'' : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Tensoring arbitrary maps of graded components in one total degree. -/
def cochainTensorDegreeMap (f : ∀ i, P.X i ⟶ P'.X i) (g : ∀ j, Q.X j ⟶ Q'.X j) (n : ℤ) :
    (cochainTensor P Q).X n ⟶ (cochainTensor P' Q').X n :=
  HomologicalComplex₂.totalDesc _ (fun i j h => (f i ⊗ₘ g j) ≫ ιTensorObj P' Q' i j n h)

@[reassoc (attr := simp)]
lemma ι_cochainTensorDegreeMap (f : ∀ i, P.X i ⟶ P'.X i) (g : ∀ j, Q.X j ⟶ Q'.X j)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ cochainTensorDegreeMap f g n =
      (f i ⊗ₘ g j) ≫ ιTensorObj P' Q' i j n h := by
  simp [cochainTensorDegreeMap]

lemma cochainTensorDegreeMap_comp (f : ∀ i, P.X i ⟶ P'.X i)
    (g : ∀ j, Q.X j ⟶ Q'.X j) (f' : ∀ i, P'.X i ⟶ P''.X i)
    (g' : ∀ j, Q'.X j ⟶ Q''.X j) (n : ℤ) :
    cochainTensorDegreeMap f g n ≫ cochainTensorDegreeMap f' g' n =
      cochainTensorDegreeMap (fun i => f i ≫ f' i) (fun j => g j ≫ g' j) n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [ι_cochainTensorDegreeMap_assoc, ι_cochainTensorDegreeMap,
    tensorHom_comp_tensorHom_assoc]

@[simp]
lemma cochainTensorDegreeMap_id (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (fun j => 𝟙 (Q.X j)) n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp

lemma cochainTensorDegreeMap_eq (f : P ⟶ P') (g : Q ⟶ Q') (n : ℤ) :
    cochainTensorDegreeMap f.f g.f n = (cochainTensorMap f g).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ι_cochainTensorDegreeMap, ιTensorObj_cochainTensorMap]

lemma cochainTensorDegreeMap_add_left (f f' : ∀ i, P.X i ⟶ P'.X i)
    (g : ∀ j, Q.X j ⟶ Q'.X j) (n : ℤ) :
    cochainTensorDegreeMap (fun i => f i + f' i) g n =
      cochainTensorDegreeMap f g n + cochainTensorDegreeMap f' g n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [comp_add, ι_cochainTensorDegreeMap, tensorHom_def]
  rw [MonoidalPreadditive.add_whiskerRight, add_comp, add_comp]

lemma cochainTensorDegreeMap_add_right (f : ∀ i, P.X i ⟶ P'.X i)
    (g g' : ∀ j, Q.X j ⟶ Q'.X j) (n : ℤ) :
    cochainTensorDegreeMap f (fun j => g j + g' j) n =
      cochainTensorDegreeMap f g n + cochainTensorDegreeMap f g' n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [comp_add, ι_cochainTensorDegreeMap, tensorHom_def]
  rw [MonoidalPreadditive.whiskerLeft_add, comp_add, add_comp]

end SerrePositivity
