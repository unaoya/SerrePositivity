module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWordNormalForm
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerWordWeights

/-!
# Schur 生成射と入力の重みの上限

## 概要
Berger–Fresse §1.1 の正規化と Berger–Moerdijk §1 の Schur 表示で、入力の重みを保つ。

## 方針
正規化された係数の基底から始め、対角置換不変性と線形性で任意の係数へ広げる。

## 規約
係数の重みを零とし、入力の重複を数える。

## 使われ方
セル代数の演算の合成と微分の重みの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open scoped TensorProduct
attribute [local implicit_reducible] SymmetricSequence SymmetricSequence.level
variable {A : Type u} [CommRing A]

/-- The homogeneous Schur generator is invariant under the simultaneous input permutation. -/
lemma schurGenerator_diagonal_apply (P : SymmetricSequence (Complex A))
    (K : Complex A) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p r i : ℤ) (h : p + r = i) (u : (P.level n).X p) (v : (power K n).X r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i (ιTensorObj (P.level n) (power K n) p r i h
      ((P.map (FiniteBijection.permutation n σ)).f p u ⊗ₜ[A]
        (permutationAction K n σ).asIso.hom.f r v)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i (ιTensorObj (P.level n) (power K n) p r i h (u ⊗ₜ[A] v)) := by
  have he := congrArg (fun f => f.f i
    (ιTensorObj (P.level n) (power K n) p r i h (u ⊗ₜ[A] v)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_diagonal A P K n σ)
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i
    ((cochainTensorMap (P.map (FiniteBijection.permutation n σ))
      (permutationAction K n σ).asIso.hom).f i
        (ιTensorObj (P.level n) (power K n) p r i h (u ⊗ₜ[A] v))) = _ at he
  erw [cochainTensorMap_apply_ι] at he
  exact he

namespace BarrattEccles
variable {K : Complex A} {I : ℤ → Type u}
  (b : ∀ i, Module.Basis (I i) A (K.X i)) (w : (Σ i, I i) → ℕ)

/-- A normalized coefficient applied to a bounded input lies in the same Schur weight span. -/
lemma schurNormalizedGenerator_mem_basisWeightSpan (i : ℤ) (n q : ℕ)
    (a : ULift.{u} (BasedNondegenerate n q)) (N : ℕ)
    {v : (power K n).X (i + q)}
    (hv : v ∈ basisWeightSpan (powerGradedBasis b n (i + q))
      (powerGradedWeight w n (i + q)) N) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i
      (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)
        (equivariantBasis A n q (a, 1) ⊗ₜ[A] v)) ∈
      basisWeightSpan (schurWordBasis b i) (schurWordWeight w) N := by
  let f : (power K n).X (i + q) →ₗ[A] ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K).X i :=
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i).hom ∘ₗ
      (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)).hom ∘ₗ
        (TensorProduct.mk A _ _ (equivariantBasis A n q (a, 1)))
  change f v ∈ _
  apply map_mem_basisWeightSpan (powerGradedBasis b n (i + q)) (schurWordBasis b i)
    (powerGradedWeight w n (i + q)) (schurWordWeight w) f ?_ N hv
  intro z
  have hz := basis_mem_basisWeightSpan (schurWordBasis b i) (schurWordWeight w)
    (schurNonpositiveWordIndex i n q (a, z))
  rw [schurWordBasis_nonpositive, schurWordWeight_nonpositive] at hz
  exact hz

/-- An arbitrary nonpositive coefficient preserves the bound on the total input weight. -/
lemma schurGenerator_mem_basisWeightSpan (i : ℤ) (n q : ℕ)
    (u : (complex A n).X (-(q : ℤ))) (N : ℕ)
    {v : (power K n).X (i + q)}
    (hv : v ∈ basisWeightSpan (powerGradedBasis b n (i + q))
      (powerGradedWeight w n (i + q)) N) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i
      (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)
        (u ⊗ₜ[A] v)) ∈ basisWeightSpan (schurWordBasis b i) (schurWordWeight w) N := by
  let S := basisWeightSpan (schurWordBasis b i) (schurWordWeight w) N
  let f : (complex A n).X (-(q : ℤ)) →ₗ[A] ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K).X i :=
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i).hom ∘ₗ
      (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)).hom ∘ₗ
        ((TensorProduct.mk A _ _).flip v)
  have hs : Submodule.span A (Set.range (equivariantBasis A n q)) ≤ S.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, g⟩, rfl⟩
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i
      (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)
        (equivariantBasis A n q (a, g) ⊗ₜ[A] v)) ∈ S
    have h := schurGenerator_diagonal_apply (sequence A) K n g
      (-(q : ℤ)) (i + q) i (by omega) (equivariantBasis A n q (a, g)) v
    rw [sequence_map_permutation] at h
    erw [equivariantBasis_rightAction] at h
    rw [mul_inv_cancel] at h
    rw [← h]
    exact schurNormalizedGenerator_mem_basisWeightSpan b w i n q a N
      (permutationAction_mem_basisWeightSpan b w n g (i + q) N hv)
  rw [(equivariantBasis A n q).span_eq] at hs
  exact hs (show u ∈ (⊤ : Submodule A ((complex A n).X (-(q : ℤ)))) from trivial)

/-- The same bound holds in every coefficient degree, with the positive degrees zero. -/
lemma schurGenerator_mem_basisWeightSpan_all (p r i : ℤ) (h : p + r = i)
    (n : ℕ) (u : ((sequence A).level n).X p) (N : ℕ) {v : (power K n).X r}
    (hv : v ∈ basisWeightSpan (powerGradedBasis b n r) (powerGradedWeight w n r) N) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i
      (ιTensorObj ((sequence A).level n) (power K n) p r i h (u ⊗ₜ[A] v)) ∈
        basisWeightSpan (schurWordBasis b i) (schurWordWeight w) N := by
  by_cases hp : p ≤ 0
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
    subst p
    have hr : r = i + q := by omega
    subst r
    exact schurGenerator_mem_basisWeightSpan b w i n q u N hv
  · have hz : IsZero (((sequence A).level n).X p) := by
      change IsZero ((complex A n).X p)
      exact complex_isZero_positive A n p (by omega)
    have : Subsingleton (((sequence A).level n).X p) :=
      ModuleCat.subsingleton_of_isZero hz
    have hu : u = 0 := Subsingleton.elim _ _
    rw [hu, TensorProduct.zero_tmul, map_zero, map_zero]
    exact Submodule.zero_mem _

end BarrattEccles
end SerrePositivity.EInfinity
