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

@[simp]
lemma cochainTensorDegreeMap_zero_left (g : ∀ j, Q.X j ⟶ Q'.X j) (n : ℤ) :
    cochainTensorDegreeMap (fun i => (0 : P.X i ⟶ P'.X i)) g n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ι_cochainTensorDegreeMap]
  simp [tensorHom_def]

@[simp]
lemma cochainTensorDegreeMap_zero_right (f : ∀ i, P.X i ⟶ P'.X i) (n : ℤ) :
    cochainTensorDegreeMap f (fun j => (0 : Q.X j ⟶ Q'.X j)) n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ι_cochainTensorDegreeMap]
  simp [tensorHom_def]

/-- A two-piece graded decomposition expands the tensor square into four components. -/
lemma cochainTensorDegreeMap_partition (a b : ∀ i, P.X i ⟶ P.X i)
    (h : (fun i => a i + b i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    cochainTensorDegreeMap a a n + cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) b n +
      cochainTensorDegreeMap b (fun i => 𝟙 (P.X i)) n =
      𝟙 ((cochainTensor P P).X n) + cochainTensorDegreeMap b b n := by
  have he : cochainTensorDegreeMap a a n +
      cochainTensorDegreeMap (fun i => a i + b i) b n +
      cochainTensorDegreeMap b (fun i => a i + b i) n =
      cochainTensorDegreeMap (fun i => a i + b i) (fun i => a i + b i) n +
      cochainTensorDegreeMap b b n := by
    rw [cochainTensorDegreeMap_add_left, cochainTensorDegreeMap_add_right,
      cochainTensorDegreeMap_add_left, cochainTensorDegreeMap_add_right,
      cochainTensorDegreeMap_add_right]
    abel
  simpa only [h, cochainTensorDegreeMap_id] using he

@[simp]
lemma cochainTensorMap_zero_zero : cochainTensorMap (0 : P ⟶ P') (0 : Q ⟶ Q') = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_cochainTensorMap]
  simp [tensorHom_def]

@[simp]
lemma cochainTensorMap_zero_right (f : P ⟶ P') : cochainTensorMap f (0 : Q ⟶ Q') = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_cochainTensorMap]
  simp [tensorHom_def]

end SerrePositivity
