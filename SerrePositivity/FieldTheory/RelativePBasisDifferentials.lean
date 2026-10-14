module

public import SerrePositivity.FieldTheory.RelativePMonomialSpan
public import SerrePositivity.FieldTheory.PAdjoinDerivation
public import SerrePositivity.CommutativeAlgebra.DerivationSpan

/-! # 指定した底体上の相対p単項式基底から微分基底を構成する

単項式基底と各生成元のp乗が底体に属する条件から、補中間体と偏導分を構成する。
微分の独立性や次元を入力として要求せず、添字の有限性は次元式にのみ使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {F K ι : Type*} [Field F] [Field K] [Algebra F K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {b : ι → K}
  (B : Module.Basis (PExponent p ι) F K)
  (hB : ∀ d, B d = pMonomial b d)
  (hpow : ∀ i, ∃ a : F, b i ^ p = algebraMap F K a)

include hB in
omit [Fact p.Prime] [CharP K p] in
/-- 相対単項式基底の生成元は代数として終域を生成する。 -/
theorem adjoin_eq_top_of_pMonomialBasis : Algebra.adjoin F (Set.range b) = ⊤ := by
  have hle : Submodule.span F (Set.range B) ≤
      (Algebra.adjoin F (Set.range b)).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    rw [hB]
    exact (Algebra.adjoin F (Set.range b)).prod_mem (fun i _ ↦
      (Algebra.adjoin F (Set.range b)).pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _)
  apply top_le_iff.mp
  intro x _
  exact hle (B.span_eq.symm ▸ Submodule.mem_top)

open Classical in
include hB hpow in
/-- 相対単項式基底から、一方向だけを1に送る偏導分を構成する。 -/
theorem exists_partialDerivation_of_pMonomialBasis (i : ι) :
    ∃ δ : Derivation F K K, ∀ j, δ (b j) = if j = i then 1 else 0 := by
  classical
  let J := {j : ι // j ≠ i}
  let emb : J ↪ ι := Function.Embedding.subtype (· ≠ i)
  let E := IntermediateField.adjoin F (Set.range (b ∘ emb))
  let n : Fin p := ⟨1, (Fact.out : p.Prime).one_lt⟩
  let d : PExponent p ι := PExponent.single i n
  have hci : B.coord d (b i) = 1 := by
    rw [← show pMonomial b d = b i by simp [d, n], ← hB]
    simp
  have hzero : ∀ x : K, x ∈ E → B.coord d x = 0 := by
    have hle : Submodule.span F (Set.range (pMonomial (p := p) (b ∘ emb))) ≤
        (B.coord d).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      have hne : PExponent.embDomain emb a ≠ d := by
        intro h
        have hv := congrArg (fun z : PExponent p ι ↦ z.val i) h
        change a.val.embDomain emb i = d.val i at hv
        rw [Finsupp.embDomain_of_notMem_range _ _ _ (by
          rintro ⟨j, hj⟩; exact j.property hj)] at hv
        simp [d, PExponent.single, n] at hv
      change B.coord d (pMonomial (b ∘ emb) a) = 0
      rw [← pMonomial_embDomain b emb a, ← hB]
      simp [Module.Basis.coord_apply, hne]
    intro x hx
    apply hle
    have hs := adjoin_toSubmodule_eq_span_pMonomial_of_pow_mem (b ∘ emb)
      (fun j ↦ hpow (emb j))
    exact hs ▸ hx
  have hnot : b i ∉ Set.range (algebraMap E K) := by
    rintro ⟨x, hx⟩
    exact one_ne_zero (hci.symm.trans (hzero _ (hx ▸ x.property)))
  have hadjoin : Algebra.adjoin E {b i} = ⊤ := by
    have hle : Algebra.adjoin F (Set.range b) ≤
        (Algebra.adjoin E {b i}).restrictScalars F := by
      apply Algebra.adjoin_le
      rintro _ ⟨j, rfl⟩
      change b j ∈ Algebra.adjoin E {b i}
      by_cases hj : j = i
      · subst j; exact Algebra.subset_adjoin (Set.mem_singleton _)
      · exact (Algebra.adjoin E {b i}).algebraMap_mem
          (⟨b j, IntermediateField.subset_adjoin F _ ⟨⟨j, hj⟩, rfl⟩⟩ : E)
    apply top_le_iff.mp
    intro x _
    exact hle ((adjoin_eq_top_of_pMonomialBasis B hB).symm ▸ Algebra.mem_top)
  obtain ⟨a, ha⟩ := hpow i
  obtain ⟨δ, hδ⟩ := exists_derivation_primeRoot_of_adjoin_eq_top (b i)
    (algebraMap F E a) (by simpa using ha) hnot hadjoin
  refine ⟨δ.restrictScalars F, ?_⟩
  intro j
  by_cases hj : j = i
  · subst j; simpa using hδ
  · have hz := δ.map_algebraMap
      (⟨b j, IntermediateField.subset_adjoin F _ ⟨⟨j, hj⟩, rfl⟩⟩ : E)
    simpa [hj] using hz

/-- 構成済みの相対偏導分を選ぶ。 -/
def partialDerivationOfPMonomialBasis (i : ι) : Derivation F K K :=
  (exists_partialDerivation_of_pMonomialBasis B hB hpow i).choose

open Classical in
@[simp] theorem partialDerivationOfPMonomialBasis_apply (i j : ι) :
    partialDerivationOfPMonomialBasis B hB hpow i (b j) = if j = i then 1 else 0 :=
  (exists_partialDerivation_of_pMonomialBasis B hB hpow i).choose_spec j

include hB hpow in
/-- 相対単項式基底の生成元の微分は独立。 -/
theorem linearIndependent_differential_of_pMonomialBasis :
    LinearIndependent K (fun i ↦ KaehlerDifferential.D F K (b i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have h := congrArg (partialDerivationOfPMonomialBasis B hB hpow i).liftKaehlerDifferential hg
  simpa [hi] using h

/-- 指定底体上の相対単項式基底から、生成元の微分の基底を構成する。 -/
def kaehlerBasisOfPMonomialBasis : Module.Basis ι K (KaehlerDifferential F K) :=
  Module.Basis.mk (linearIndependent_differential_of_pMonomialBasis B hB hpow) (by
    have hs : Submodule.span K
        (Set.range (fun i ↦ KaehlerDifferential.D F K (b i))) = ⊤ := by
      simpa only [← Set.range_comp, Function.comp_def] using
        span_kaehlerDifferential_of_adjoin_eq_top (Set.range b)
          (adjoin_eq_top_of_pMonomialBasis B hB)
    rw [hs])

@[simp] theorem kaehlerBasisOfPMonomialBasis_apply (i : ι) :
    kaehlerBasisOfPMonomialBasis B hB hpow i = KaehlerDifferential.D F K (b i) :=
  Module.Basis.mk_apply _ _ _

include B hB hpow in
/-- 有限な相対p単項式基底に対する微分の次元。 -/
theorem finrank_differential_of_pMonomialBasis [Fintype ι] :
    Module.finrank K (KaehlerDifferential F K) = Fintype.card ι :=
  Module.finrank_eq_card_basis (kaehlerBasisOfPMonomialBasis B hB hpow)

end SerrePositivity
