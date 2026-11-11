module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
概要：全タプルの増大整数鎖の、頂点を先頭に付ける縮約。
方針：境界のうち先頭を削除する項を分離し、残る項の符号を反転する。
規約：鎖の添字はタプルの長さであり、長さ零が増大項に対応する。
使われ方：標準開の Čech 比較で、各タプルの頂点集合内にホモトピーを作る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped BigOperators

variable {ι : Type*}

/-- 長さ `k` のタプルを生成元とする自由整数加群。 -/
abbrev CechTupleChains (ι : Type*) (k : ℕ) := (Fin k → ι) →₀ ℤ

/-- 各頂点の削除の交代和で定める境界。 -/
def cechTupleBoundary (k : ℕ) : CechTupleChains ι (k + 1) →ₗ[ℤ] CechTupleChains ι k :=
  Finsupp.linearCombination ℤ fun t ↦
    ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • Finsupp.single (t ∘ i.succAbove) 1

private theorem cechTupleBoundary_single (k : ℕ) (t : Fin (k + 1) → ι) :
    cechTupleBoundary k (Finsupp.single t 1) =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • Finsupp.single (t ∘ i.succAbove) 1 := by
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul]

/-- 固定頂点を各タプルの先頭に付ける。 -/
def cechTuplePrepend (v : ι) (k : ℕ) :
    CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι (k + 1) :=
  Finsupp.lmapDomain ℤ ℤ (Fin.cons v)

private theorem cechTuplePrepend_single (v : ι) (k : ℕ) (t : Fin k → ι) :
    cechTuplePrepend v k (Finsupp.single t 1) = Finsupp.single (Fin.cons v t) 1 := by
  simp only [cechTuplePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/--
概要：正の長さのタプルで境界と先頭追加の反交換式を与える。
方針：先頭を削除した項が恒等で、他の削除が先頭追加と反対の符号で対応する。
規約：長さ一の式には、長さ零への増大写像が入る。
使われ方：各タプルの頂点集合内でサイクルの境界前像を作る。
-/
theorem cechTupleBoundary_prepend (v : ι) (k : ℕ) :
    (cechTupleBoundary (k + 1)).comp (cechTuplePrepend v (k + 1)) +
      (cechTuplePrepend v k).comp (cechTupleBoundary k) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t c
  rw [← Finsupp.smul_single_one t c, map_smul, map_smul]
  congr 1
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    cechTuplePrepend_single, cechTupleBoundary_single, map_sum, map_smul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.cons_comp_succ,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove,
    Fin.removeNth, Function.comp_def, Finset.sum_neg_distrib, add_assoc, neg_add_cancel, add_zero]

end SerrePositivity.AlgebraicGeometry
