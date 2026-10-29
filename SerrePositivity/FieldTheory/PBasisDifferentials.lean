module

public import SerrePositivity.FieldTheory.PBasis
public import SerrePositivity.FieldTheory.PMonomialSpan
public import SerrePositivity.FieldTheory.PAdjoinDerivation
public import SerrePositivity.CommutativeAlgebra.DerivationSpan

/-! # 相対 p 単項式基底と Kähler 微分の基底

概要：`K` が底体 `F` 上で相対 p 単項式基底 `{bᵈ}`（各 `b i ^ p ∈ F`）を持つとき、
`D (b i)` は `Ω_{K/F}` の基底になる。各方向 `i` について、`b i` を1、他の `b j` を0に送る偏導分を定義する。
方針：`b i` 以外の生成元が張る補中間体 `E` 上で `b i` は p 乗根で全体を生成するので、
`primeRootDerivation` を `F` へ係数制限したものが偏導分になる。
絶対 p 基底（`F = K^p`）はこの特殊化として扱う。
規約：添字の有限性は次元の式にだけ使う。
使われ方：共有限な中間係数体上の微分の基底（CommutativeAlgebra の Cofinite 系）、p 乗部分体上の定数の判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section OverPowers

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- 任意の基礎環上の導分も、p 乗部分体の元を消す。 -/
theorem derivation_eq_zero_on_pPowerSubfield
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (δ : Derivation R K V) (x : K) (hx : x ∈ pPowerSubfield K p) : δ x = 0 := by
  obtain ⟨y, rfl⟩ := (mem_pPowerSubfield K p x).mp hx
  exact derivation_pow_char_eq_zero p δ y

/-- 任意の基礎環上の導分を、同じ写像のまま p 乗部分体上の導分にする。
p 乗部分体の作用は、K の作用から制限した標準作用を用いる。 -/
def derivationOverPowers
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (δ : Derivation R K V) : Derivation (pPowerSubfield K p) K V where
  toFun := δ
  map_add' := map_add δ
  map_smul' c x := by
    rw [Algebra.smul_def]
    have hc : δ (algebraMap (pPowerSubfield K p) K c) = 0 :=
      derivation_eq_zero_on_pPowerSubfield δ _ c.property
    rw [δ.leibniz, hc, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

@[simp] theorem derivationOverPowers_apply
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (δ : Derivation R K V) (x : K) : derivationOverPowers (p := p) δ x = δ x := rfl

end OverPowers

section Relative

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

variable (b) in
/-- `b i` 以外の生成元が `F` 上で張る補中間体。 -/
def pMonomialComplementField (i : ι) : IntermediateField F K :=
  IntermediateField.adjoin F (Set.range fun j : {j : ι // j ≠ i} ↦ b j)

omit [Fact p.Prime] [CharP K p] in
theorem mem_pMonomialComplementField {i j : ι} (hj : j ≠ i) :
    b j ∈ pMonomialComplementField (F := F) b i :=
  IntermediateField.subset_adjoin F _ ⟨⟨j, hj⟩, rfl⟩

include hB hpow in
omit [CharP K p] in
/-- `b i` は補中間体に属さない（座標 `d = single i 1` で区別する）。 -/
theorem notMem_range_pMonomialComplementField (i : ι) :
    b i ∉ Set.range (algebraMap (pMonomialComplementField (F := F) b i) K) := by
  classical
  let J := {j : ι // j ≠ i}
  let emb : J ↪ ι := Function.Embedding.subtype (· ≠ i)
  let n : Fin p := ⟨1, (Fact.out : p.Prime).one_lt⟩
  let d : PExponent p ι := PExponent.single i n
  have hci : B.coord d (b i) = 1 := by
    rw [← show pMonomial b d = b i by simp [d, n], ← hB]
    simp
  have hzero : ∀ x : K, x ∈ pMonomialComplementField (F := F) b i → B.coord d x = 0 := by
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
  rintro ⟨x, hx⟩
  exact one_ne_zero (hci.symm.trans (hzero _ (hx ▸ x.property)))

include hB in
omit [Fact p.Prime] [CharP K p] in
/-- `b i` は補中間体上で全体を生成する。 -/
theorem adjoin_pMonomialComplementField_eq_top (i : ι) :
    Algebra.adjoin (pMonomialComplementField (F := F) b i) {b i} = ⊤ := by
  have hle : Algebra.adjoin F (Set.range b) ≤
      (Algebra.adjoin (pMonomialComplementField (F := F) b i) {b i}).restrictScalars F := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    change b j ∈ Algebra.adjoin (pMonomialComplementField (F := F) b i) {b i}
    by_cases hj : j = i
    · subst j; exact Algebra.subset_adjoin (Set.mem_singleton _)
    · exact (Algebra.adjoin _ {b i}).algebraMap_mem
        (⟨b j, mem_pMonomialComplementField hj⟩ : pMonomialComplementField (F := F) b i)
  apply top_le_iff.mp
  intro x _
  exact hle ((adjoin_eq_top_of_pMonomialBasis B hB).symm ▸ Algebra.mem_top)

include hpow in
omit [Fact p.Prime] [CharP K p] in
theorem pow_mem_pMonomialComplementField (i : ι) :
    b i ^ p ∈ pMonomialComplementField (F := F) b i := by
  obtain ⟨a, ha⟩ := hpow i
  exact ha ▸ (pMonomialComplementField (F := F) b i).algebraMap_mem a

/-- 方向 `i` の偏導分：`b i` を1、他の `b j` を0に送る `F` 上の導分。 -/
def partialDerivationOfPMonomialBasis (i : ι) : Derivation F K K :=
  (primeRootDerivation (b i)
    (⟨b i ^ p, pow_mem_pMonomialComplementField hpow i⟩ : pMonomialComplementField (F := F) b i)
    rfl (notMem_range_pMonomialComplementField B hB hpow i)
    (adjoin_pMonomialComplementField_eq_top B hB i)).restrictScalars F

open Classical in
@[simp] theorem partialDerivationOfPMonomialBasis_apply (i j : ι) :
    partialDerivationOfPMonomialBasis B hB hpow i (b j) = if j = i then 1 else 0 := by
  by_cases hj : j = i
  · subst j
    rw [ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]
    exact primeRootDerivation_self (b i)
      (⟨b i ^ p, pow_mem_pMonomialComplementField hpow i⟩ : pMonomialComplementField (F := F) b i)
      rfl (notMem_range_pMonomialComplementField B hB hpow i)
      (adjoin_pMonomialComplementField_eq_top B hB i)
  · simpa [partialDerivationOfPMonomialBasis, hj] using
      (primeRootDerivation (b i)
        (⟨b i ^ p, pow_mem_pMonomialComplementField hpow i⟩ :
          pMonomialComplementField (F := F) b i)
        rfl (notMem_range_pMonomialComplementField B hB hpow i)
        (adjoin_pMonomialComplementField_eq_top B hB i)).map_algebraMap
          (⟨b j, mem_pMonomialComplementField hj⟩ : pMonomialComplementField (F := F) b i)

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

end Relative

section Absolute

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable {ι : Type*} {b : ι → K}

/-- 絶対 p 基底の偏導分（`F = K^p` の場合）。 -/
def IsPBasis.partialDerivation (hb : IsPBasis K p b) (i : ι) :
    Derivation (pPowerSubfield K p) K K :=
  partialDerivationOfPMonomialBasis hb.basis hb.basis_apply
    (fun j ↦ ⟨⟨b j ^ p, (mem_pPowerSubfield K p _).mpr ⟨b j, rfl⟩⟩, rfl⟩) i

open Classical in
@[simp] theorem IsPBasis.partialDerivation_apply (hb : IsPBasis K p b) (i j : ι) :
    hb.partialDerivation i (b j) = if j = i then 1 else 0 :=
  partialDerivationOfPMonomialBasis_apply _ _ _ i j

end Absolute

end SerrePositivity
