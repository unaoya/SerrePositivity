module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NaturalTruncation

/-!
# 有限頭部の指定成分による展開

## 概要
高い横次数の行が零なら、積全複体の各元を有限個の指定成分の和に展開できる。

## 方針
積全複体の指定行射影で等式を判定する。

## 規約
指定された積全複体を保つ。内部次数の有界性は使わない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部のテンソル比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped BigOperators

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 高い横次数の行が零なら、元は有限個の指定成分の和である。 -/
theorem finite_component_expansion (K : CochainComplex (Complex R) ℕ) (N : ℕ)
    (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (q : ℤ) (x : (total K).X q) :
    x = ∑ n ∈ Finset.range N, insert K q n (componentπ K n q x) := by
  apply ext
  intro m
  by_cases hm : m < N
  · rw [map_sum]
    rw [Finset.sum_eq_single m]
    · exact (insert_component_self K q m _).symm
    · intro n hn hnm
      exact insert_component_ne K q n m (Ne.symm hnm) _
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hm))
  · have hz := (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) (q-m)).map_isZero
      (hK m (by omega))
    haveI : Subsingleton ((K.X m).X (q-m)) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _

/-- 任意の有限頭部の元は、残した元の行の有限和に展開できる。 -/
theorem head_component_expansion (K : CochainComplex (Complex R) ℕ) (N : ℕ)
    (q : ℤ) (x : (total (RowTruncation.head K N)).X q) :
    x = ∑ n ∈ Finset.range N, insert (RowTruncation.head K N) q n
      (componentπ (RowTruncation.head K N) n q x) :=
  finite_component_expansion _ N (RowTruncation.head_isZero K N) q x

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
