module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurPowerWordLift
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
# 自由 Barratt–Eccles 代数の演算の重み保存

## 概要
Berger–Moerdijk §1 の自由代数の作用は、元の入力の語の総重みを増やさない。

## 方針
Schur 語のテンソル基底を内側の演算族へ持ち上げ、演算の合成式を適用する。

## 規約
係数は任意で、零入力を含む。

## 使われ方
セル段の基底語の微分の重み評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open ComplexWeightBasis
open scoped TensorProduct
attribute [local implicit_reducible] SymmetricSequence SymmetricSequence.level operad
variable {A : Type u} [CommRing A] {K : Complex A}

/-- Acting on a bounded tensor of free-algebra words preserves the total original input bound. -/
lemma schurAction_mem_basisWeightSpan (b : ComplexWeightBasis K)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : ((operad A).arity n).X p)
    (N : ℕ) {v : (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) n).X r}
    (hv : v ∈ basisWeightSpan (powerGradedBasis (schurWordBasis b.basis) n r)
      (powerGradedWeight (schurWeightBasis b).weight n r) N) :
    ((operad A).schurAction K n).f i
      (ιTensorObj ((operad A).arity n) (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) n)
        p r i h (u ⊗ₜ[A] v)) ∈
      basisWeightSpan (schurWordBasis b.basis i) (schurWordWeight b.weight) N := by
  let f : (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) n).X r →ₗ[A]
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K).X i :=
    (((operad A).schurAction K n).f i).hom ∘ₗ
      (ιTensorObj ((operad A).arity n) (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) n)
        p r i h).hom ∘ₗ (TensorProduct.mk A _ _ u)
  change f v ∈ _
  apply map_mem_basisWeightSpan (powerGradedBasis (schurWordBasis b.basis) n r)
    (schurWordBasis b.basis i) (powerGradedWeight (schurWeightBasis b).weight n r)
    (schurWordWeight b.weight) f ?_ N hv
  intro x
  obtain ⟨s, y, hy, he⟩ := schurPowerWord_lift b n r x
  let c := family n (fun j => (arityWeightBasis (s j)).tensor (b.power (s j)))
  have ht := tensorGradedInclusion_mem (arityGradedBasis n) c.basis
    (fun _ => 0) c.weight p r i h 0 _
    (mem_basisWeightSpan_zero (arityGradedBasis n p) 0 u) hy
  have ho := preserves_schurOperationGenerator b n s i _ ht
  simp only [zero_add] at ho
  have heq := congrArg (fun z => z.f i
    (ιTensorObj ((operad A).arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => (operad A).arity (s j) ⊗ power K (s j)))
      p r i h (u ⊗ₜ[A] y))) ((operad A).schurInputGenerator_action K n s)
  change ((operad A).schurAction K n).f i
    ((cochainTensorMap (𝟙 ((operad A).arity n))
      ((operad A).schurInputGenerator K n s)).f i
      (ιTensorObj ((operad A).arity n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => (operad A).arity (s j) ⊗ power K (s j)))
        p r i h (u ⊗ₜ[A] y))) = _ at heq
  erw [cochainTensorMap_apply_ι] at heq
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, he] at heq
  change ((operad A).schurAction K n).f i
    (ιTensorObj ((operad A).arity n) (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) n)
      p r i h (u ⊗ₜ[A] powerGradedBasis (schurWordBasis b.basis) n r x)) ∈ _
  erw [heq]
  exact ho

end SerrePositivity.EInfinity.BarrattEccles
