module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseWordEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurActionGenerators

/-!
# 自由代数の語を指定生成元で評価する式

## 概要
Berger–Moerdijk §1 の Schur 生成射を、自由代数の生成元への作用で表す。

## 方針
既存の生成元上の作用の式を斉次元で評価し、テンソル語の自然性を使う。

## 規約
係数も入力語も任意であり、零入力を含む。

## 使われ方
実際のセル段の基底語を付加生成元の像で評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {K : Complex A} {I : ℤ → Type u}

/-- A Schur word is the operation applied to the corresponding free generators. -/
lemma schurGenerator_eq_actionValue (b : ∀ i, Module.Basis (I i) A (K.X i))
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : (P.arity n).X p)
    (x : powerGradedIndex I n r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n).f i (ιTensorObj (P.arity n) (power K n) p r i h
      (u ⊗ₜ[A] powerGradedBasis b n r x)) =
    (P.schurAction K n).f i
      (ιTensorObj (P.arity n) (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n) p r i h
        (u ⊗ₜ[A] powerWordValue ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
          (fun i z => (P.schurUnit K).f i (b i z)) n r x)) := by
  have hc := congrArg (fun z => z.f i
    (ιTensorObj (P.arity n) (power K n) p r i h
      (u ⊗ₜ[A] powerGradedBasis b n r x))) (P.schurAction_generators K n)
  change (P.schurAction K n).f i
    ((cochainTensorMap (𝟙 (P.arity n)) (TensorPowers.map (P.schurUnit K) n)).f i
      (ιTensorObj (P.arity n) (power K n) p r i h
        (u ⊗ₜ[A] powerGradedBasis b n r x))) = _ at hc
  rw [cochainTensorMap_apply_ι] at hc
  have hn := powerWordValue_naturality (P.schurUnit K) (fun i z => b i z) n r x
  rw [powerWordValue_basis] at hn
  rw [hn] at hc
  exact hc.symm

end SerrePositivity.EInfinity.Operad
