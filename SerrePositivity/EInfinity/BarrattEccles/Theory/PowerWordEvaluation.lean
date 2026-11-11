module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerWordWeights

/-!
# 指定生成元でのテンソル語の評価と微分

## 概要
Berger–Moerdijk §1 の入力の語を、複体の指定された斉次元で評価する。

## 方針
各入力とその微分の重みの上限から、斉次テンソルの Leibniz 則で語の評価を扱う。

## 規約
入力の微分に同じ上限を仮定し、零入力を含める。

## 使われ方
実際の付加生成元からセル代数の基底語の微分を評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- Evaluate the specified right-associated word on its homogeneous input elements. -/
def powerWordValue (K : Complex A) {I : ℤ → Type u} (g : ∀ i, I i → K.X i) :
    ∀ n i, powerGradedIndex I n i → (power K n).X i
  | 0, i, x => unitDegreeBasis (A := A) i x
  | n + 1, i, ⟨a, z, y⟩ =>
      ιTensorObj K (power K n) a.1.1 a.1.2 i a.2
        (g a.1.1 z ⊗ₜ[A] powerWordValue K g n a.1.2 y)

/-- Evaluating a word on the basis itself is the specified tensor-power basis. -/
lemma powerWordValue_basis {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (n : ℕ) (i : ℤ)
    (x : powerGradedIndex I n i) :
    powerWordValue K (fun i z => b i z) n i x = powerGradedBasis b n i x := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    obtain ⟨a, z, y⟩ := x
    rw [powerWordValue, powerGradedBasis_succ]
    erw [tensorGradedBasis_apply]
    rw [ih]

variable {K : Complex A} {I J : ℤ → Type u}
  (b : ∀ i, Module.Basis (J i) A (K.X i)) (w : (Σ i, J i) → ℕ)
  (g : ∀ i, I i → K.X i) (v : (Σ i, I i) → ℕ)
  (hg : ∀ i z, g i z ∈ basisWeightSpan (b i) (fun z => w ⟨i, z⟩) (v ⟨i, z⟩))

include hg

/-- A word of bounded homogeneous inputs has the sum of their weight bounds. -/
lemma powerWordValue_mem (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) :
    powerWordValue K g n i x ∈
      basisWeightSpan (powerGradedBasis b n i) (powerGradedWeight w n i)
        (powerGradedWeight v n i x) := by
  induction n generalizing i with
  | zero => exact basis_mem_basisWeightSpan (unitDegreeBasis (A := A) i) (fun _ => 0) x
  | succ n ih =>
    obtain ⟨a, z, y⟩ := x
    have h := tensorGradedInclusion_mem b (powerGradedBasis b n) w
      (powerGradedWeightFamily w n) a.1.1 a.1.2 i a.2
      (v ⟨a.1.1, z⟩) (powerGradedWeight v n a.1.2 y) (hg _ _) (ih _ y)
    simp only [powerWordValue, powerGradedBasis_succ, powerGradedWeightFamily,
      powerGradedWeight_succ, tensorGradedWeight] at h ⊢
    exact h

/-- If each specified input and its differential satisfy the same bound,
so does the word differential. -/
lemma powerWordValue_d_mem
    (hdg : ∀ i z, K.d i (i + 1) (g i z) ∈
      basisWeightSpan (b (i + 1)) (fun z => w ⟨i + 1, z⟩) (v ⟨i, z⟩))
    (n : ℕ) (i : ℤ) (x : powerGradedIndex I n i) :
    (power K n).d i (i + 1) (powerWordValue K g n i x) ∈
      basisWeightSpan (powerGradedBasis b n (i + 1)) (powerGradedWeight w n (i + 1))
        (powerGradedWeight v n i x) := by
  induction n generalizing i with
  | zero =>
    change (𝟙_ (Complex A)).d i (i + 1) _ ∈ _
    erw [HomologicalComplex.single_obj_d]
    exact Submodule.zero_mem _
  | succ n ih =>
    obtain ⟨a, z, y⟩ := x
    have ht := powerWordValue_mem b w g v hg n a.1.2 y
    have h₁ := tensorGradedInclusion_mem b (powerGradedBasis b n) w
      (powerGradedWeightFamily w n) (a.1.1 + 1) a.1.2 (i + 1) (by omega)
      (v ⟨a.1.1, z⟩) (powerGradedWeight v n a.1.2 y) (hdg _ _) ht
    have h₂ := tensorGradedInclusion_mem b (powerGradedBasis b n) w
      (powerGradedWeightFamily w n) a.1.1 (a.1.2 + 1) (i + 1) (by omega)
      (v ⟨a.1.1, z⟩) (powerGradedWeight v n a.1.2 y) (hg _ _) (ih _ y)
    have hs := (basisWeightSpan (tensorGradedBasis b (powerGradedBasis b n) (i + 1))
      (tensorGradedWeight w (powerGradedWeightFamily w n) (i + 1))
      (v ⟨a.1.1, z⟩ + powerGradedWeight v n a.1.2 y)).add_mem h₁
        (zsmul_mem h₂ (a.1.1.negOnePow.val))
    change (cochainTensor K (power K n)).d i (i + 1)
      (ιTensorObj K (power K n) a.1.1 a.1.2 i a.2
        (g a.1.1 z ⊗ₜ[A] powerWordValue K g n a.1.2 y)) ∈ _
    rw [cochainTensor_d_apply_ι]
    simp only [powerGradedBasis_succ, powerGradedWeightFamily, powerGradedWeight_succ,
      tensorGradedWeight, Units.smul_def] at hs ⊢
    exact hs

end SerrePositivity.EInfinity
