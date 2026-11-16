module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 剰余係数の基底による元の基底環線形射の判定

## 概要
剰余係数加群からの基底環線形射は、同じ元の剰余係数基底の値で決まる。

## 方針
基底展開の有限個の係数を元の基底環へ持ち上げ、元の線形性を使う。

## 規約
終域が剰余係数の加群であるとは仮定しない。

## 使われ方
被覆上の完備形式の同じ基底で、元のHT写像の二つのB線形射を照合する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
variable {B : Type u} [CommRing B] (I : Ideal B)
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
variable [Module (B ⧸ I) M] [Module B N] {ι : Type v}

/-- 剰余係数の同じ基底の値が一致するなら、元の基底環線形射は一致する。 -/
theorem quotientBasis_linearMap_ext (b : Module.Basis ι (B ⧸ I) M) :
    letI := Module.compHom M (Ideal.Quotient.mk I)
    ∀ g h : M →ₗ[B] N, (∀ i, g (b i) = h (b i)) → g = h := by
  letI := Module.compHom M (Ideal.Quotient.mk I)
  intro g h hb
  apply LinearMap.ext
  intro x
  have hx : (b.repr x).sum (fun i a => a • b i) = x := by
    simpa only [Finsupp.linearCombination_apply] using b.linearCombination_repr x
  calc
    g x = g ((b.repr x).sum (fun i a => a • b i)) := congrArg g hx.symm
    _ = h ((b.repr x).sum (fun i a => a • b i)) := by
      simp only [Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((b.repr x) i)
      rw [← ha]
      change g (a • b i) = h (a • b i)
      rw [map_smul, map_smul, hb]
    _ = h x := congrArg h hx

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
