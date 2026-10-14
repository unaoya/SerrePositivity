module

public import SerrePositivity.PerfectComplex.TensorDegreeMaps
public import SerrePositivity.PerfectComplex.TensorTriple

/-! # Tensor maps of arbitrary graded triples -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]
variable {P P' P'' Q Q' Q'' T T' T'' : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Tensor three graded maps; none need commute with the differentials. -/
def cochainTensorTripleDegreeMap (f : ∀ i, P.X i ⟶ P'.X i)
    (g : ∀ j, Q.X j ⟶ Q'.X j) (t : ∀ k, T.X k ⟶ T'.X k) (n : ℤ) :
    (cochainTensor (cochainTensor P Q) T).X n ⟶
      (cochainTensor (cochainTensor P' Q') T').X n :=
  cochainTensorDegreeMap (fun s => cochainTensorDegreeMap f g s) t n

lemma cochainTensorTripleDegreeMap_comp
    (f : ∀ i, P.X i ⟶ P'.X i) (g : ∀ j, Q.X j ⟶ Q'.X j)
    (t : ∀ k, T.X k ⟶ T'.X k) (f' : ∀ i, P'.X i ⟶ P''.X i)
    (g' : ∀ j, Q'.X j ⟶ Q''.X j) (t' : ∀ k, T'.X k ⟶ T''.X k) (n : ℤ) :
    cochainTensorTripleDegreeMap f g t n ≫ cochainTensorTripleDegreeMap f' g' t' n =
      cochainTensorTripleDegreeMap (fun i => f i ≫ f' i)
        (fun j => g j ≫ g' j) (fun k => t k ≫ t' k) n := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_comp]

@[simp]
lemma cochainTensorTripleDegreeMap_id (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    cochainTensorTripleDegreeMap (fun i => 𝟙 (P.X i)) (fun j => 𝟙 (Q.X j))
      (fun k => 𝟙 (T.X k)) n = 𝟙 _ := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_id]

lemma cochainTensorTripleDegreeMap_eq (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T') (n : ℤ) :
    cochainTensorTripleDegreeMap f.f g.f t.f n = (cochainTensorTripleMap f g t).f n := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_eq]

lemma cochainTensorTripleDegreeMap_add_first
    (f f' : ∀ i, P.X i ⟶ P'.X i) (g : ∀ j, Q.X j ⟶ Q'.X j)
    (t : ∀ k, T.X k ⟶ T'.X k) (n : ℤ) :
    cochainTensorTripleDegreeMap (fun i => f i + f' i) g t n =
      cochainTensorTripleDegreeMap f g t n + cochainTensorTripleDegreeMap f' g t n := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_add_left]

lemma cochainTensorTripleDegreeMap_add_second
    (f : ∀ i, P.X i ⟶ P'.X i) (g g' : ∀ j, Q.X j ⟶ Q'.X j)
    (t : ∀ k, T.X k ⟶ T'.X k) (n : ℤ) :
    cochainTensorTripleDegreeMap f (fun j => g j + g' j) t n =
      cochainTensorTripleDegreeMap f g t n + cochainTensorTripleDegreeMap f g' t n := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_add_right,
    cochainTensorDegreeMap_add_left]

lemma cochainTensorTripleDegreeMap_add_third
    (f : ∀ i, P.X i ⟶ P'.X i) (g : ∀ j, Q.X j ⟶ Q'.X j)
    (t t' : ∀ k, T.X k ⟶ T'.X k) (n : ℤ) :
    cochainTensorTripleDegreeMap f g (fun k => t k + t' k) n =
      cochainTensorTripleDegreeMap f g t n + cochainTensorTripleDegreeMap f g t' n := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_add_right]

@[simp]
lemma cochainTensorTripleDegreeMap_zero_first (g : ∀ j, Q.X j ⟶ Q'.X j)
    (t : ∀ k, T.X k ⟶ T'.X k) (n : ℤ) :
    cochainTensorTripleDegreeMap (fun i => (0 : P.X i ⟶ P'.X i)) g t n = 0 := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_zero_left]

@[simp]
lemma cochainTensorTripleDegreeMap_zero_second (f : ∀ i, P.X i ⟶ P'.X i)
    (t : ∀ k, T.X k ⟶ T'.X k) (n : ℤ) :
    cochainTensorTripleDegreeMap f (fun j => (0 : Q.X j ⟶ Q'.X j)) t n = 0 := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_zero_right,
    cochainTensorDegreeMap_zero_left]

@[simp]
lemma cochainTensorTripleDegreeMap_zero_third (f : ∀ i, P.X i ⟶ P'.X i)
    (g : ∀ j, Q.X j ⟶ Q'.X j) (n : ℤ) :
    cochainTensorTripleDegreeMap f g (fun k => (0 : T.X k ⟶ T'.X k)) n = 0 := by
  simp only [cochainTensorTripleDegreeMap, cochainTensorDegreeMap_zero_right]

/-- Two complementary graded pieces expand the tensor cube into eight components. -/
lemma cochainTensorTripleDegreeMap_partition (a b : ∀ i, P.X i ⟶ P.X i)
    (h : (fun i => a i + b i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    cochainTensorTripleDegreeMap a a a n + cochainTensorTripleDegreeMap b a a n +
      cochainTensorTripleDegreeMap a b a n + cochainTensorTripleDegreeMap a a b n +
      cochainTensorTripleDegreeMap b b a n + cochainTensorTripleDegreeMap b a b n +
      cochainTensorTripleDegreeMap a b b n + cochainTensorTripleDegreeMap b b b n =
        𝟙 ((cochainTensor (cochainTensor P P) P).X n) := by
  have he : cochainTensorTripleDegreeMap (fun i => a i + b i) (fun i => a i + b i)
      (fun i => a i + b i) n =
      cochainTensorTripleDegreeMap a a a n + cochainTensorTripleDegreeMap b a a n +
      cochainTensorTripleDegreeMap a b a n + cochainTensorTripleDegreeMap a a b n +
      cochainTensorTripleDegreeMap b b a n + cochainTensorTripleDegreeMap b a b n +
      cochainTensorTripleDegreeMap a b b n + cochainTensorTripleDegreeMap b b b n := by
    simp only [cochainTensorTripleDegreeMap_add_first,
      cochainTensorTripleDegreeMap_add_second, cochainTensorTripleDegreeMap_add_third]
    abel
  rw [h, cochainTensorTripleDegreeMap_id] at he
  exact he.symm

end SerrePositivity
