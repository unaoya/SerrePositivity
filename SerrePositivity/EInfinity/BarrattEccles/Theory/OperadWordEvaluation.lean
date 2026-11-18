module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.PowerWordEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
# 指定生成元でのオペラッドの語の微分

## 概要
Berger–Moerdijk §1 の演算を斉次生成元で評価した語の微分を扱う。

## 方針
作用の複体射としての可換性と、テンソル語の Leibniz 則を使う。

## 規約
演算の重み保存と、指定入力とその微分の上限を仮定する。

## 使われ方
セル代数の基底語の微分が重みを増やさないことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} (X : P.Algebra)

/-- Evaluate a homogeneous coefficient operation on the specified input word. -/
def evaluatedWord {I : ℤ → Type u} (g : ∀ i, I i → X.carrier.X i)
    (p r i : ℤ) (h : p + r = i) (n : ℕ) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) : X.carrier.X i :=
  (X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h
    (u ⊗ₜ[A] powerWordValue X.carrier g n r x))

variable {I J : ℤ → Type u}
  (b : ∀ i, Module.Basis (J i) A (X.carrier.X i)) (w : (Σ i, J i) → ℕ)
  (g : ∀ i, I i → X.carrier.X i) (v : (Σ i, I i) → ℕ)
  (hg : ∀ i z, g i z ∈ basisWeightSpan (b i) (fun z => w ⟨i, z⟩) (v ⟨i, z⟩))
  (ha : ∀ (p r i : ℤ) (h : p + r = i) (n : ℕ) (u : (P.arity n).X p) (N : ℕ)
      {y : (power X.carrier n).X r},
    y ∈ basisWeightSpan (powerGradedBasis b n r) (powerGradedWeight w n r) N →
    (X.action n).f i (ιTensorObj (P.arity n) (power X.carrier n) p r i h (u ⊗ₜ[A] y)) ∈
      basisWeightSpan (b i) (fun z => w ⟨i, z⟩) N)

include hg ha

/-- The coefficient differential and the input differential preserve the same word bound. -/
lemma evaluatedWord_d_mem
    (hdg : ∀ i z, X.carrier.d i (i + 1) (g i z) ∈
      basisWeightSpan (b (i + 1)) (fun z => w ⟨i + 1, z⟩) (v ⟨i, z⟩))
    (p r i : ℤ) (h : p + r = i) (n : ℕ) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    X.carrier.d i (i + 1) (evaluatedWord X g p r i h n u x) ∈
      basisWeightSpan (b (i + 1)) (fun z => w ⟨i + 1, z⟩)
        (powerGradedWeight v n r x) := by
  let N := powerGradedWeight v n r x
  have hv := powerWordValue_mem (K := X.carrier) b w g v hg n r x
  have hdv := powerWordValue_d_mem (K := X.carrier) b w g v hg hdg n r x
  have h₁ := ha (p + 1) r (i + 1) (by omega) n ((P.arity n).d p (p + 1) u) N hv
  have h₂ := ha p (r + 1) (i + 1) (by omega) n u N hdv
  have hc := congrArg (fun f => f
    (ιTensorObj (P.arity n) (power X.carrier n) p r i h
      (u ⊗ₜ[A] powerWordValue X.carrier g n r x))) ((X.action n).comm i (i + 1))
  change X.carrier.d i (i + 1) (evaluatedWord X g p r i h n u x) =
    (X.action n).f (i + 1)
      ((cochainTensor (P.arity n) (power X.carrier n)).d i (i + 1)
        (ιTensorObj (P.arity n) (power X.carrier n) p r i h
          (u ⊗ₜ[A] powerWordValue X.carrier g n r x))) at hc
  rw [cochainTensor_d_apply_ι] at hc
  rw [hc, map_add, Units.smul_def, map_zsmul]
  exact (basisWeightSpan (b (i + 1)) (fun z => w ⟨i + 1, z⟩) N).add_mem h₁
    (zsmul_mem h₂ p.negOnePow.val)

end SerrePositivity.EInfinity.Operad
