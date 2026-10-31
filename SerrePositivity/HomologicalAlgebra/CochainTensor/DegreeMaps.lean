module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-! # 次数ごとの成分のテンソル写像

## 概要

微分との両立を要求しない次数ごとの成分の写像のテンソル（二因子と三因子）を作る。次数ごとの分裂をテンソル積で使うためのもの。

## 方針

全複体の各次数の直和因子ごとに写像を定める。

## 規約

鎖写像である必要はない。

## 使われ方

`CochainTensor/ShortExact`、PerfectComplex のテンソル。
-/

@[expose] public noncomputable section

universe u

section CochainTensorDegreeMapsPart

set_option backward.isDefEq.respectTransparency false

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

end SerrePositivity

end CochainTensorDegreeMapsPart

section CochainTensorTripleDegreeMapsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

/-- Reconstruct the low pieces using one unrestricted quotient slot at a time. -/
lemma cochainTensorTripleDegreeMap_sparse_partition
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (a b : ∀ i, P.X i ⟶ P.X i)
    (h : (fun i => a i + b i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    cochainTensorTripleDegreeMap a a a n +
      cochainTensorTripleDegreeMap b (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) n +
      cochainTensorTripleDegreeMap (fun i => 𝟙 (P.X i)) b (fun i => 𝟙 (P.X i)) n +
      cochainTensorTripleDegreeMap (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) b n =
      𝟙 ((cochainTensor (cochainTensor P P) P).X n) +
        cochainTensorTripleDegreeMap b b a n + cochainTensorTripleDegreeMap b a b n +
        cochainTensorTripleDegreeMap a b b n + cochainTensorTripleDegreeMap b b b n +
        cochainTensorTripleDegreeMap b b b n := by
  have he := cochainTensorTripleDegreeMap_partition a b h n
  rw [← h]
  simp only [cochainTensorTripleDegreeMap_add_first,
    cochainTensorTripleDegreeMap_add_second, cochainTensorTripleDegreeMap_add_third]
  rw [← he]
  abel

end SerrePositivity

end CochainTensorTripleDegreeMapsPart
