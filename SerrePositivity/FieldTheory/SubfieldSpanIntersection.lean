module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # 下向き有向な部分体族に沿う線形包の交わり

一つの部分体上で独立な共通の有限族を固定する。
より小さい部分体での展開の一意性により、共通の元の係数は部分体族の交わりに属する。
体の標数やp-rankは要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K τ ι : Type*} [Field K]

/-- 大きい部分体上の独立性があれば、線形包への所属は各係数の所属に帰着する。 -/
theorem sum_mul_mem_subfield_span_iff [Fintype τ]
    (E S : Subfield K) (hES : E ≤ S) (v : τ → K)
    (hv : LinearIndependent S v) (c : τ → K) (hc : ∀ t, c t ∈ S) :
    (∑ t, c t * v t) ∈ Submodule.span E (Set.range v) ↔ ∀ t, c t ∈ E := by
  classical
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp h
    let dS : τ → S := fun t ↦ ⟨d t, hES (d t).property⟩
    let cS : τ → S := fun t ↦ ⟨c t, hc t⟩
    have heq : (∑ t, dS t • v t) = ∑ t, cS t • v t := by
      simpa [Algebra.smul_def, Subfield.algebraMap_ofSubfield, dS, cS] using hd
    have hdc : dS = cS := hv.fintypeLinearCombination_injective heq
    intro t
    have ht := congrArg (fun f : τ → S ↦ (f t : K)) hdc
    change (d t : K) = c t at ht
    exact ht ▸ (d t).property
  · intro h
    apply (Submodule.mem_span_range_iff_exists_fun E).mpr
    refine ⟨fun t ↦ ⟨c t, h t⟩, ?_⟩
    simp [Algebra.smul_def, Subfield.algebraMap_ofSubfield]

/-- 下向き有向な族の全ての線形包に属す元は、交わり上の線形包に属する。
独立性は族の一つの部分体上で確認すればよい。 -/
theorem mem_all_subfield_spans_iff [Finite τ]
    (E : ι → Subfield K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (v : τ → K) (hind : ∃ j, LinearIndependent (E j) v) (x : K) :
    (∀ i, x ∈ Submodule.span (E i) (Set.range v)) ↔
      x ∈ Submodule.span ↥(⨅ i, E i) (Set.range v) := by
  classical
  let := Fintype.ofFinite τ
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := hind
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (E j)).mp (hx j)
    let cK : τ → K := fun t ↦ c t
    have hcK : (∑ t, cK t * v t) = x := by
      simpa [Algebra.smul_def, Subfield.algebraMap_ofSubfield, cK] using hc
    have hcoeff (t : τ) : cK t ∈ ⨅ i, E i := by
      apply Subfield.mem_iInf.mpr
      intro i
      obtain ⟨k, hki, hkj⟩ := hdir i j
      have hk : ∀ t, cK t ∈ E k :=
        (sum_mul_mem_subfield_span_iff (E k) (E j) hkj v hj cK
          (fun t ↦ (c t).property)).mp (hcK.symm ▸ hx k)
      exact hki (hk t)
    apply (Submodule.mem_span_range_iff_exists_fun ↥(⨅ i, E i)).mpr
    refine ⟨fun t ↦ ⟨cK t, hcoeff t⟩, ?_⟩
    simpa [Algebra.smul_def, Subfield.algebraMap_ofSubfield] using hcK
  · intro hx i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ↥(⨅ i, E i)).mp hx
    apply (Submodule.mem_span_range_iff_exists_fun (E i)).mpr
    refine ⟨fun t ↦ ⟨c t, (Subfield.mem_iInf.mp (c t).property) i⟩, ?_⟩
    simpa [Algebra.smul_def, Subfield.algebraMap_ofSubfield] using hc

end SerrePositivity
