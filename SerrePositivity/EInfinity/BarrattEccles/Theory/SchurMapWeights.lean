module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWeightedBasis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedPowerMap

/-!
# 入力の重みを保つ射と Schur 関手

## 概要
Berger–Moerdijk §1 の自由代数の底の Schur 関手は、入力の語の重みの上限を保つ。

## 方針
正規化された基底語と Schur 生成射の自然性を使い、入力のテンソル冪へ帰着する。

## 規約
入力基底の添字は、出力基底の添字と異なってよい。

## 使われ方
実際のセル段の包含で語の重みが増えないことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open ComplexWeightBasis
open scoped TensorProduct
attribute [local implicit_reducible] SymmetricSequence SymmetricSequence.level
variable {A : Type u} [CommRing A] {K L : Complex A}

/-- The Schur functor preserves total input bounds for every bound-preserving generator map. -/
lemma preserves_schurMap {b : ComplexWeightBasis K} {c : ComplexWeightBasis L}
    {f : K ⟶ L} (hf : b.Preserves c f) :
    (schurWeightBasis b).Preserves (schurWeightBasis c)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).map f) := by
  intro i N x hx
  apply map_mem_basisWeightSpan (schurWordBasis b.basis i) (schurWordBasis c.basis i)
    (schurWordWeight b.weight) (schurWordWeight c.weight)
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).map f).f i).hom ?_ N hx
  intro z
  obtain ⟨n, q, a, v, rfl⟩ := schurWordIndex_exists_nonpositive i z
  rw [schurWordBasis_nonpositive, schurWordWeight_nonpositive]
  have he := congrArg (fun z => z.f i
    (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)
      (equivariantBasis A n q (a, 1) ⊗ₜ[A] powerGradedBasis b.basis n (i + q) v)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality A (sequence A) f n)
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).map f).f i
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i _) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) L n).f i
      ((cochainTensorMap (𝟙 ((sequence A).level n)) (TensorPowers.map f n)).f i
        (ιTensorObj ((sequence A).level n) (power K n) (-(q : ℤ)) (i + q) i (by omega)
          (equivariantBasis A n q (a, 1) ⊗ₜ[A] powerGradedBasis b.basis n (i + q) v))) at he
  erw [cochainTensorMap_apply_ι] at he
  rw [he]
  exact schurGenerator_mem_basisWeightSpan c.basis c.weight i n q
    (equivariantBasis A n q (a, 1)) _
    (hf.powerMap n (i + q) _ (basis_mem_basisWeightSpan
      (powerGradedBasis b.basis n (i + q)) (powerGradedWeight b.weight n (i + q)) v))

end SerrePositivity.EInfinity.BarrattEccles
