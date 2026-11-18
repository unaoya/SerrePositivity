module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurOperationWeights

/-!
# Schur 語のテンソルを内側の演算族へ持ち上げる

## 概要
Berger–Moerdijk §1 の Schur 入力生成射で、指定された語の基底を持ち上げる。

## 方針
各入力を正規化された係数と元の入力の語へ戻し、テンソル冪の長さで帰納する。

## 規約
持ち上げの入力重みは、元の Schur 語の総重みの上限以内。

## 使われ方
自由代数の作用の重み保存を、演算の合成生成射の重み保存へ帰着する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open ComplexWeightBasis
open scoped TensorProduct
attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SymmetricSequence SymmetricSequence.level operad
variable {A : Type u} [CommRing A] {K : Complex A}

/-- A bounded tail lift extends by the normalized first Schur word. -/
lemma schurPowerWord_lift_step (b : ComplexWeightBasis K) (n : ℕ) (s : Fin (n + 1) → ℕ)
    (p r i : ℤ) (hi : p + r = i) (q : ℕ)
    (c : ULift.{u} (BasedNondegenerate (s 0) q))
    (v : powerGradedIndex b.index (s 0) (p + q))
    (t : powerGradedIndex (SchurWordIndex b.index) n r)
    (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j =>
      (operad A).arity (s j.succ) ⊗ power K (s j.succ))).X r)
    (hy : y ∈ basisWeightSpan
      ((family n (fun j => (arityWeightBasis (s j.succ)).tensor (b.power (s j.succ)))).basis r)
      (fun z => (family n (fun j =>
        (arityWeightBasis (s j.succ)).tensor (b.power (s j.succ)))).weight ⟨r, z⟩)
      (powerGradedWeight (schurWeightBasis b).weight n r t))
    (he : ((operad A).schurInputGenerator K n (fun j => s j.succ)).f r y =
      powerGradedBasis (schurWordBasis b.basis) n r t) :
    ∃ z : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => (operad A).arity (s j) ⊗ power K (s j))).X i,
      z ∈ basisWeightSpan
        ((family (n + 1) (fun j => (arityWeightBasis (s j)).tensor (b.power (s j)))).basis i)
        (fun z => (family (n + 1) (fun j =>
          (arityWeightBasis (s j)).tensor (b.power (s j)))).weight ⟨i, z⟩)
        (powerGradedWeight (schurWeightBasis b).weight (n + 1) i
          ⟨⟨(p, r), hi⟩, schurNonpositiveWordIndex p (s 0) q (c, v), t⟩) ∧
      ((operad A).schurInputGenerator K (n + 1) s).f i z =
        powerGradedBasis (schurWordBasis b.basis) (n + 1) i
          ⟨⟨(p, r), hi⟩, schurNonpositiveWordIndex p (s 0) q (c, v), t⟩ := by
  let head : ((operad A).arity (s 0) ⊗ power K (s 0)).X p :=
    ιTensorObj ((operad A).arity (s 0)) (power K (s 0)) (-(q : ℤ)) (p + q) p
      (by omega) (equivariantBasis A (s 0) q (c, 1) ⊗ₜ[A]
        powerGradedBasis b.basis (s 0) (p + q) v)
  have hh : head ∈ basisWeightSpan
      (((arityWeightBasis (s 0)).tensor (b.power (s 0))).basis p)
      (fun z => ((arityWeightBasis (s 0)).tensor (b.power (s 0))).weight ⟨p, z⟩)
      (powerGradedWeight b.weight (s 0) (p + q) v) := by
    have h := tensorGradedInclusion_mem (arityGradedBasis (s 0))
      (powerGradedBasis b.basis (s 0)) (fun _ => 0) (powerGradedWeightFamily b.weight (s 0))
      (-(q : ℤ)) (p + q) p (by omega) 0 (powerGradedWeight b.weight (s 0) (p + q) v)
      (mem_basisWeightSpan_zero (arityGradedBasis (s 0) (-(q : ℤ))) 0
        (equivariantBasis A (s 0) q (c, 1)))
      (basis_mem_basisWeightSpan (powerGradedBasis b.basis (s 0) (p + q))
        (powerGradedWeight b.weight (s 0) (p + q)) v)
    simp only [zero_add] at h
    exact h
  refine ⟨ιTensorObj ((operad A).arity (s 0) ⊗ power K (s 0))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => (operad A).arity (s j.succ) ⊗ power K (s j.succ)))
    p r i hi (head ⊗ₜ[A] y), ?_, ?_⟩
  · have hw : powerGradedWeight (schurWeightBasis b).weight (n + 1) i
        ⟨⟨(p, r), hi⟩, schurNonpositiveWordIndex p (s 0) q (c, v), t⟩ =
        powerGradedWeight b.weight (s 0) (p + q) v +
          powerGradedWeight (schurWeightBasis b).weight n r t := by
      change schurWordWeight b.weight (schurNonpositiveWordIndex p (s 0) q (c, v)) +
        powerGradedWeight (schurWeightBasis b).weight n r t = _
      rw [schurWordWeight_nonpositive]
    rw [hw]
    exact tensorGradedInclusion_mem
      ((arityWeightBasis (s 0)).tensor (b.power (s 0))).basis
      (family n (fun j => (arityWeightBasis (s j.succ)).tensor (b.power (s j.succ)))).basis
      ((arityWeightBasis (s 0)).tensor (b.power (s 0))).weight
      (family n (fun j => (arityWeightBasis (s j.succ)).tensor (b.power (s j.succ)))).weight
      p r i hi _ _ hh hy
  · change (cochainTensorMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K (s 0))
      ((operad A).schurInputGenerator K n (fun j => s j.succ))).f i
      (ιTensorObj ((operad A).arity (s 0) ⊗ power K (s 0))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => (operad A).arity (s j.succ) ⊗ power K (s j.succ)))
        p r i hi (head ⊗ₜ[A] y)) = _
    erw [cochainTensorMap_apply_ι]
    rw [he]
    have hh' := schurWordBasis_nonpositive b.basis p (s 0) q (c, v)
    change schurWordBasis b.basis p (schurNonpositiveWordIndex p (s 0) q (c, v)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K (s 0)).f p head at hh'
    rw [← hh', powerGradedBasis_succ]
    exact (tensorGradedBasis_apply
      (K := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K)
      (L := power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K) n)
      (schurWordBasis b.basis) (powerGradedBasis (schurWordBasis b.basis) n) i
      ⟨⟨(p, r), hi⟩, schurNonpositiveWordIndex p (s 0) q (c, v), t⟩).symm

/-- Each power of Schur basis words has a bounded preimage in its inner arity family. -/
lemma schurPowerWord_lift (b : ComplexWeightBasis K) (n : ℕ) (i : ℤ)
    (x : powerGradedIndex (SchurWordIndex b.index) n i) :
    ∃ (s : Fin n → ℕ)
      (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => (operad A).arity (s j) ⊗ power K (s j))).X i),
      y ∈ basisWeightSpan
        ((family n (fun j => (arityWeightBasis (s j)).tensor (b.power (s j)))).basis i)
        (fun z => (family n (fun j =>
          (arityWeightBasis (s j)).tensor (b.power (s j)))).weight ⟨i, z⟩)
        (powerGradedWeight (schurWeightBasis b).weight n i x) ∧
      ((operad A).schurInputGenerator K n s).f i y =
        powerGradedBasis (schurWordBasis b.basis) n i x := by
  induction n generalizing i with
  | zero =>
    refine ⟨Fin.elim0, unitDegreeBasis i x, ?_, rfl⟩
    exact mem_basisWeightSpan_zero (unitDegreeBasis i) 0 _
  | succ n ih =>
    obtain ⟨a, z, t⟩ := x
    obtain ⟨k, q, c, v, rfl⟩ := schurWordIndex_exists_nonpositive a.1.1 z
    obtain ⟨s, y, hy, he⟩ := ih a.1.2 t
    have hs := schurPowerWord_lift_step b n (Fin.cons k s)
      a.1.1 a.1.2 i a.2 q c v t
    dsimp only at hs
    obtain ⟨z, hz, hez⟩ := hs y hy he
    exact ⟨Fin.cons k s, z, hz, hez⟩

end SerrePositivity.EInfinity.BarrattEccles
