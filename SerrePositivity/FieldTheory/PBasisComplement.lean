module

public import SerrePositivity.FieldTheory.PAdjoinDerivation
public import Mathlib.Logic.Equiv.Option

/-! # p-basis の一方向を除いた中間体

単項式基底の座標で残した元を検出し、補中間体に属さないことを示す。
-/

@[expose] public section
namespace SerrePositivity

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable {ι : Type*} (b : ι → K)

/-- 一つの添字を除いた p-basis の元が生成する中間体。 -/
def pBasisComplementField (i : ι) : IntermediateField (pPowerSubfield K p) K :=
  pMonomialIntermediateField (p := p) (fun j : {j : ι // j ≠ i} ↦ b j)

theorem mem_pBasisComplementField {i j : ι} (hji : j ≠ i) :
    b j ∈ pBasisComplementField (p := p) b i := by
  rw [pBasisComplementField, pMonomialIntermediateField_eq_adjoin]
  exact IntermediateField.subset_adjoin _ _ ⟨⟨j, hji⟩, rfl⟩

variable {b}

/-- 部分族が使わない方向の単項式座標は、その部分族の生成体上で零。 -/
theorem IsPBasis.coord_eq_zero_of_mem_subfamilyField (hb : IsPBasis K p b)
    {κ : Type*} (e : κ ↪ ι) (d : PExponent p ι) (i : ι)
    (hi : i ∉ Set.range e) (hdi : d.val i ≠ 0)
    {x : K} (hx : x ∈ pMonomialIntermediateField (p := p) (b ∘ e)) :
    hb.basis.coord d x = 0 := by
  classical
  let c := hb.basis.coord d
  have hc : pMonomialSpan (p := p) (b ∘ e) ≤ c.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hne : PExponent.embDomain e a ≠ d := by
      intro h
      have hv := congrArg (fun z : PExponent p ι ↦ z.val i) h
      change a.val.embDomain e i = d.val i at hv
      rw [Finsupp.embDomain_of_notMem_range _ _ _ hi] at hv
      exact hdi hv.symm
    change c (pMonomial (b ∘ e) a) = 0
    rw [← pMonomial_embDomain b e a, ← hb.basis_apply (PExponent.embDomain e a)]
    simp only [c, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    exact ite_eq_right hne
  exact hc hx

/-- 除いた元は補中間体に属さない。単項式基底の独立性から従う。 -/
theorem IsPBasis.notMem_complementField (hb : IsPBasis K p b) (i : ι) :
    b i ∉ pBasisComplementField (p := p) b i := by
  classical
  let n : Fin p := ⟨1, (Fact.out : p.Prime).one_lt⟩
  let d0 : PExponent p ι := PExponent.single i n
  let c := hb.basis.coord d0
  let e : {j : ι // j ≠ i} ↪ ι := Function.Embedding.subtype (· ≠ i)
  have hci : c (b i) = 1 := by
    have heq : pMonomial b d0 = b i := by simp [d0, n]
    rw [← heq, ← hb.basis_apply d0]
    simp only [c, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  intro hi
  have houtside : i ∉ Set.range e := by
    rintro ⟨j, hj⟩
    exact j.property hj
  have hz := hb.coord_eq_zero_of_mem_subfamilyField e d0 i houtside
    (by simp [d0, PExponent.single, n]) hi
  exact one_ne_zero (hci.symm.trans hz)

/-- 補中間体に除いた元を添加すれば、代数として元の体全体を生成する。 -/
theorem IsPBasis.adjoin_complement_eq_top (hb : IsPBasis K p b) (i : ι) :
    Algebra.adjoin (pBasisComplementField (p := p) b i) {b i} = ⊤ := by
  classical
  let E := pBasisComplementField (p := p) b i
  let A := Algebra.adjoin E {b i}
  have hle : Algebra.adjoin (pPowerSubfield K p) (Set.range b) ≤
      A.restrictScalars (pPowerSubfield K p) := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    change b j ∈ A
    by_cases hj : j = i
    · subst j
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · exact A.algebraMap_mem (⟨b j, mem_pBasisComplementField b hj⟩ : E)
  apply top_le_iff.mp
  intro x _
  exact hle (hb.adjoin_eq_top.symm ▸ Algebra.mem_top)

/-- 補中間体上に、残した元を1、残りのp-basis元を0に送る導分を構成する。 -/
theorem IsPBasis.exists_complementDerivation (hb : IsPBasis K p b) (i : ι) :
    ∃ δ : Derivation (pBasisComplementField (p := p) b i) K K,
      δ (b i) = 1 ∧ ∀ j, j ≠ i → δ (b j) = 0 := by
  let E := pBasisComplementField (p := p) b i
  let a : E := ⟨(b i) ^ p, E.algebraMap_mem
    ⟨(b i) ^ p, (mem_pPowerSubfield K p _).mpr ⟨b i, rfl⟩⟩⟩
  have hx : b i ∉ Set.range (algebraMap E K) := by
    rintro ⟨y, hy⟩
    exact hb.notMem_complementField i (hy ▸ y.property)
  let δ := primeRootDerivation (b i) a rfl hx (hb.adjoin_complement_eq_top i)
  have hδ : δ (b i) = 1 := primeRootDerivation_self (b i) a rfl hx (hb.adjoin_complement_eq_top i)
  refine ⟨δ, hδ, ?_⟩
  intro j hji
  exact δ.map_algebraMap (⟨b j, mem_pBasisComplementField b hji⟩ : E)

end SerrePositivity
