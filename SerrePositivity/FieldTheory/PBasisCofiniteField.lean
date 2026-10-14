module

public import SerrePositivity.FieldTheory.PBasisComplement
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # p-basis の有限個の方向を残す中間係数体

有限集合eの外のp-basis元をp乗部分体へ添加する。残した有限個の元は
この体上で整であり、元の体全体を生成する。p-basis全体の有限性は不要。
-/

@[expose] public section
namespace SerrePositivity
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} (b : ι → K)

/-- eの外のp-basis元とp乗部分体からなる中間体。 -/
def pBasisCofiniteField (e : Finset ι) : IntermediateField (pPowerSubfield K p) K :=
  pMonomialIntermediateField (p := p) (fun j : {j : ι // j ∉ e} ↦ b j)

theorem mem_pBasisCofiniteField (e : Finset ι) {i : ι} (hi : i ∉ e) :
    b i ∈ pBasisCofiniteField (p := p) b e := by
  rw [pBasisCofiniteField, pMonomialIntermediateField_eq_adjoin]
  exact IntermediateField.subset_adjoin _ _ ⟨⟨i, hi⟩, rfl⟩

/-- 残す方向を増やすと、係数体は小さくなる。 -/
theorem pBasisCofiniteField_antitone {e f : Finset ι} (hef : e ⊆ f) :
    pBasisCofiniteField (p := p) b f ≤ pBasisCofiniteField (p := p) b e := by
  rw [pBasisCofiniteField, pBasisCofiniteField, pMonomialIntermediateField_eq_adjoin,
    pMonomialIntermediateField_eq_adjoin]
  apply IntermediateField.adjoin.mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j, fun hj ↦ j.property (hef hj)⟩, rfl⟩

variable {b}

/-- 残した有限個の元を中間係数体へ添加すれば、元の体全体になる。 -/
theorem IsPBasis.adjoin_cofiniteField_eq_top (hb : IsPBasis K p b) (e : Finset ι) :
    Algebra.adjoin (pBasisCofiniteField (p := p) b e)
      (Set.range (fun j : e ↦ b j)) = ⊤ := by
  classical
  let E := pBasisCofiniteField (p := p) b e
  let A := Algebra.adjoin E (Set.range (fun j : e ↦ b j))
  have hle : Algebra.adjoin (pPowerSubfield K p) (Set.range b) ≤
      A.restrictScalars (pPowerSubfield K p) := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    change b j ∈ A
    by_cases hj : j ∈ e
    · exact Algebra.subset_adjoin ⟨⟨j, hj⟩, rfl⟩
    · exact A.algebraMap_mem (⟨b j, mem_pBasisCofiniteField b e hj⟩ : E)
  apply top_le_iff.mp
  intro x _
  exact hle (hb.adjoin_eq_top.symm ▸ Algebra.mem_top)

/-- 有限個の方向を残す拡大は有限。整性と有限生成添加のMathlib定理を使う。 -/
theorem IsPBasis.finite_cofiniteField (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Finite (pBasisCofiniteField (p := p) b e) K := by
  classical
  let E := pBasisCofiniteField (p := p) b e
  have hint (x : K) : IsIntegral E x := by
    let a : E := ⟨x ^ p, E.algebraMap_mem
      ⟨x ^ p, (mem_pPowerSubfield K p _).mpr ⟨x, rfl⟩⟩⟩
    exact isIntegral_of_prime_pow_eq x a rfl
  have h := fg_adjoin_of_finite (Set.finite_range (fun j : e ↦ b j))
    (fun x _ ↦ hint x)
  rw [hb.adjoin_cofiniteField_eq_top e] at h
  exact ⟨h⟩

/-- 空集合では全てのp-basis元を添加するので、中間体は元の体全体。 -/
theorem IsPBasis.cofiniteField_empty (hb : IsPBasis K p b) :
    pBasisCofiniteField (p := p) b ∅ = ⊤ := by
  have hle : Algebra.adjoin (pPowerSubfield K p) (Set.range b) ≤
      (pBasisCofiniteField (p := p) b ∅).toSubalgebra := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact mem_pBasisCofiniteField b ∅ (Finset.notMem_empty i)
  apply top_le_iff.mp
  intro x _
  exact hle (hb.adjoin_eq_top.symm ▸ Algebra.mem_top)

/-- 係数体の元の単項式座標は、残した方向を使う指数では零になる。 -/
theorem IsPBasis.coord_eq_zero_of_mem_cofiniteField (hb : IsPBasis K p b)
    (e : Finset ι) (d : PExponent p ι) (hd : ∃ i ∈ e, d.val i ≠ 0)
    {x : K} (hx : x ∈ pBasisCofiniteField (p := p) b e) : hb.basis.coord d x = 0 := by
  classical
  obtain ⟨i, hie, hdi⟩ := hd
  let emb : {j : ι // j ∉ e} ↪ ι := Function.Embedding.subtype (· ∉ e)
  have hi : i ∉ Set.range emb := by
    rintro ⟨j, rfl⟩
    exact j.property hie
  exact hb.coord_eq_zero_of_mem_subfamilyField emb d i hi hdi hx

/-- 全ての有限集合に対する中間係数体の交わりは、p乗部分体そのもの。 -/
theorem IsPBasis.iInf_cofiniteField_eq_bot (hb : IsPBasis K p b) :
    (⨅ e : Finset ι, pBasisCofiniteField (p := p) b e) = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxe (e : Finset ι) : x ∈ pBasisCofiniteField (p := p) b e :=
    (iInf_le (fun e ↦ pBasisCofiniteField (p := p) b e) e) hx
  let a := hb.basis.repr x 0
  apply IntermediateField.mem_bot.mpr
  refine ⟨a, ?_⟩
  change (a : K) = x
  symm
  apply hb.basis.repr.injective
  have ha : (a : K) = a • hb.basis 0 := by
    rw [hb.basis_apply, pMonomial_zero]
    change (a : K) = (a : K) * 1
    exact (mul_one _).symm
  rw [ha, map_smul, hb.basis.repr_self]
  ext d
  by_cases hd : d = 0
  · subst d
    simp [a]
  · have hex : ∃ i, d.val i ≠ 0 := by
      by_contra hh
      apply hd
      apply Subtype.ext
      ext i
      by_contra hi
      exact hh ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hc := hb.coord_eq_zero_of_mem_cofiniteField {i} d ⟨i, by simp, hi⟩ (hxe {i})
    simpa [Module.Basis.coord_apply, Finsupp.smul_apply, Finsupp.single_apply, hd, Ne.symm hd]
      using hc

/-- 係数体族は、有限集合の和を使って下向きに有向。 -/
theorem pBasisCofiniteField_directed :
    Directed (· ≥ ·) (pBasisCofiniteField (p := p) b) := by
  classical
  intro e f
  exact ⟨e ∪ f, pBasisCofiniteField_antitone b Finset.subset_union_left,
    pBasisCofiniteField_antitone b Finset.subset_union_right⟩

end SerrePositivity
