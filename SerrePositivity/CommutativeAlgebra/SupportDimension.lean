module

public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.RingTheory.KrullDimension.Module

/-! # 短完全列と台の次元

短完全列の中央の次元は両端の次元の最大値である。
台の素イデアル鎖は最小の素イデアルを含む側にすべて入る、という議論で証明する。
有限長テンソル積から、二つの素イデアルの和の根基が極大イデアルとなることも示す。
-/

public section

universe u

namespace SerrePositivity

section FiniteLengthSupport

section support

open TensorProduct

variable {R : Type u} [CommRing R]

/-- 有限生成加群のテンソル積の台は、両方の台の共通部分に等しい。
各素イデアルの剰余体へのテンソル積で台への所属を判定し、体上では非零なベクトル空間どうしの
テンソル積が非零であることを用いる。Noether 性は不要である。 -/
theorem support_tensorProduct (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    Module.support R (M ⊗[R] N) = Module.support R M ∩ Module.support R N := by
  ext p
  let K := p.asIdeal.ResidueField
  let e : (K ⊗[R] M) ⊗[K] (K ⊗[R] N) ≃ₗ[K] K ⊗[R] (M ⊗[R] N) :=
    (AlgebraTensorModule.tensorTensorTensorComm R R K K K M K N).trans
      (AlgebraTensorModule.congr (TensorProduct.rid K K) (LinearEquiv.refl R (M ⊗[R] N)))
  simp only [Set.mem_inter_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  constructor
  · intro h
    have ht : Nontrivial ((K ⊗[R] M) ⊗[K] (K ⊗[R] N)) := e.nontrivial_congr.mpr h
    constructor
    · by_contra hn
      have : Subsingleton (K ⊗[R] M) := not_nontrivial_iff_subsingleton.mp hn
      exact (not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton ((K ⊗[R] M) ⊗[K] (K ⊗[R] N)))) ht
    · by_contra hn
      have : Subsingleton (K ⊗[R] N) := not_nontrivial_iff_subsingleton.mp hn
      exact (not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton ((K ⊗[R] M) ⊗[K] (K ⊗[R] N)))) ht
  · rintro ⟨hM, hN⟩
    exact e.nontrivial_congr.mp inferInstance

/-- 有限長加群の台に属する素イデアルは極大である。
組成列で帰納し、単純加群の零化イデアルが極大であることと短完全列に沿う台の和集合表示を使う。 -/
theorem isMaximal_of_mem_support_of_isFiniteLength (M : Type u) [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∀ p ∈ Module.support R M, p.asIdeal.IsMaximal := by
  induction h with
  | of_subsingleton => simp [Module.support_eq_empty]
  | @of_simple_quotient M _ _ N hs hN ih =>
    intro p hp
    rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ N)
      N.injective_subtype N.mkQ_surjective] at hp
    rcases hp with hp | hp
    · exact ih p hp
    · have hmax := IsSimpleModule.annihilator_isMaximal (R := R) (M := M ⧸ N)
      have he := hmax.eq_of_le p.2.ne_top (Module.annihilator_le_of_mem_support hp)
      exact he ▸ hmax

/-- Noether 環上の有限生成加群は、その台が極大イデアルだけからなるなら有限長である。
零化イデアルによる商環は零次元 Noether 環、したがって Artin 環となる。 -/
theorem isFiniteLength_of_support_isMaximal [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ p ∈ Module.support R M, p.asIdeal.IsMaximal) : IsFiniteLength R M := by
  have : IsNoetherianRing (R ⧸ Module.annihilator R M) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsArtinianRing (R ⧸ Module.annihilator R M) := by
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro p hp
    exact h ⟨p, hp.1.1⟩ (Module.mem_support_iff_of_finite.mpr hp.1.2)
  exact isFiniteLength_of_le_radical_annihilator (Module.annihilator R M) M
    Ideal.le_radical

end support


/-- Noether 環上の有限生成加群の台が有限長加群の台に含まれるなら、その加群も有限長である。
台に属する素イデアルがすべて極大であるという有限長性の判定による。 -/
theorem isFiniteLength_of_support_subset {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N)
    (h : Module.support R M ⊆ Module.support R N) : IsFiniteLength R M :=
  isFiniteLength_of_support_isMaximal M (fun p hp =>
    isMaximal_of_mem_support_of_isFiniteLength N hN p (h hp))

end FiniteLengthSupport

section QuotientSupport

open scoped nonZeroDivisors

variable {R : Type u} [CommRing R]

/-- 加群 `M` が `R ⧸ I` 加群の構造をもち、`R` の作用がそれを経由する（`IsScalarTower`）なら、`I` は
`M` を消す：`r ∈ I` は `R ⧸ I` で零になるから。 -/
lemma quotient_action_annihilator (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    I ≤ Module.annihilator R M := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r x]
  have hz : algebraMap R (R ⧸ I) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [hz, zero_smul]

/-- 素イデアル `I` による商環 `R ⧸ I` 上で正の階数をもつ有限生成 `R` 加群 `M`（`R ⧸ I` 加群の構造が
`R` の作用と両立するもの）について、台の次元 `dim Supp M` は `dim(R ⧸ I)` に等しい。階数が正なら
`R ⧸ I`（整域）の作用は忠実なので `Ann_R M = I`、そして台の次元は `dim(R ⧸ Ann M)` に等しい
（Mathlib の `supportDim_eq_ringKrullDim_quotient_annihilator`）。正則性も局所性も要らない。
Lemma 5.2（`IntersectionMultiplicity/FiniteExtension.lean`）で次元の条件を確かめるのに使う。 -/
theorem supportDim_of_quotient_rank_pos (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M]
    (hr : 0 < Module.finrank (R ⧸ I) M) :
    Module.supportDim R M = ringKrullDim (R ⧸ I) := by
  have hf : FaithfulSMul (R ⧸ I) M := by
    by_contra hn
    exact hr.ne' (Module.finrank_eq_zero_of_not_faithfulSMul hn)
  have hann : Module.annihilator R M = I := by
    rw [← Module.comap_annihilator (R := R ⧸ I), Module.annihilator_eq_bot.mpr hf]
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, hann]

/-- 整域 `R/I` 上の有限生成ねじれ加群の台の次元は、`dim(R/I)` より少なくとも一つ低い。
有限生成性から加群全体を消す非零元を選び、零化イデアルによる商への全射に
Mathlib の非零因子による次元評価を適用する。`⊥` と無限次元も含む評価である。 -/
theorem supportDim_add_one_le_of_quotient_torsion (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M] [Module.Finite (R ⧸ I) M]
    (ht : Module.IsTorsion (R ⧸ I) M) :
    Module.supportDim R M + 1 ≤ ringKrullDim (R ⧸ I) := by
  obtain ⟨s, hs, hs0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  rw [Submodule.annihilator_top] at hs
  let f : (R ⧸ I) →+* (R ⧸ Module.annihilator R M) :=
    Ideal.Quotient.factor (quotient_action_annihilator I M)
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hz : f s = 0 := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    change Ideal.Quotient.mk _ r = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (algebraMap R (R ⧸ I)) r ∈ Module.annihilator (R ⧸ I) M at hs
    rw [Module.mem_annihilator] at hs ⊢
    intro m
    simpa only [IsScalarTower.algebraMap_smul] using hs m
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_succ_le_of_surjective f hsurj hs0 hz

/-- 整域 `R/I` 上の有限生成加群には、一般点で同じ階数をもつ自由部分加群が存在する。
余核は階数零、したがってねじれ加群となり、その台の次元に一を加えても `dim(R/I)` 以下である。
正則性・局所性・正の階数は不要。有限次元の場合には余核の次元が真に小さいことを意味する。 -/
theorem exists_genericBasis (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M] [Module.Finite (R ⧸ I) M] :
    ∃ f : (Fin (Module.finrank (R ⧸ I) M) → R ⧸ I) →ₗ[R] M,
      Function.Injective f ∧
        Module.supportDim R (M ⧸ LinearMap.range f) + 1 ≤ ringKrullDim (R ⧸ I) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R ⧸ I) (M := M) le_rfl
  let g := Fintype.linearCombination (R ⧸ I) v
  have hg : Function.Injective g := linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  refine ⟨g.restrictScalars R, hg, ?_⟩
  have hr : Module.finrank (R ⧸ I) (LinearMap.range g) = Module.finrank (R ⧸ I) M := by
    rw [← (LinearEquiv.ofInjective g hg).finrank_eq]
    simp
  have hz : Module.finrank (R ⧸ I) (M ⧸ LinearMap.range g) = 0 := by
    have := Module.finrank_quotient_add_finrank_le (LinearMap.range g)
    rw [hr] at this
    omega
  have ht := Module.finrank_eq_zero_iff_isTorsion.mp hz
  exact supportDim_add_one_le_of_quotient_torsion I (M ⧸ LinearMap.range g) ht

end QuotientSupport

open IsLocalRing TensorProduct

variable {R : Type u} [CommRing R]

/-- 短完全列の台の次元は両端の台の次元の最大値。有限生成性は不要。 -/
theorem supportDim_eq_max_of_exact
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g) :
    Module.supportDim R M₂ = max (Module.supportDim R M₁) (Module.supportDim R M₃) := by
  apply le_antisymm
  · unfold Module.supportDim Order.krullDim
    refine iSup_le fun c ↦ ?_
    have hc := (congrArg (fun s : Set (PrimeSpectrum R) ↦ c.head.val ∈ s)
      (Module.support_of_exact he hf hg)).mp c.head.property
    rcases hc with hc | hc
    · let c₁ : LTSeries (Module.support R M₁) := LTSeries.mk c.length
        (fun i ↦ ⟨(c i).val, Module.mem_support_mono (c.head_le i) hc⟩)
        (fun _ _ hij ↦ c.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim c₁).trans (le_max_left _ _)
    · let c₃ : LTSeries (Module.support R M₃) := LTSeries.mk c.length
        (fun i ↦ ⟨(c i).val, Module.mem_support_mono (c.head_le i) hc⟩)
        (fun _ _ hij ↦ c.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim c₃).trans (le_max_right _ _)
  · exact max_le (Module.supportDim_le_of_injective f hf)
      (Module.supportDim_le_of_surjective g hg)

/-- 局所環の二つの素イデアル商のテンソル積が有限長なら、その和の根基は極大イデアル。
テンソル積の台の交叉表示を使うため、テンソル積と商環の同型の選択を必要としない。 -/
theorem radical_sup_eq_maximalIdeal_of_tensor_finiteLength [IsLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hfin : Module.length R ((R ⧸ P) ⊗[R] (R ⧸ Q)) ≠ ⊤) :
    (P ⊔ Q).radical = maximalIdeal R := by
  apply le_antisymm
  · exact (Ideal.radical_mono
      (sup_le (le_maximalIdeal (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)))
        (le_maximalIdeal (Ideal.IsPrime.ne_top (inferInstance : Q.IsPrime))))).trans_eq
        (maximalIdeal.isMaximal R).isPrime.radical
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J hJ ↦ ?_
    obtain ⟨hPJQ, hJprime⟩ := hJ
    let := hJprime
    have hmem : (⟨J, hJprime⟩ : PrimeSpectrum R) ∈
        Module.support R ((R ⧸ P) ⊗[R] (R ⧸ Q)) := by
      rw [support_tensorProduct]
      constructor
      · exact Module.mem_support_iff_of_finite.mpr (by
          rw [Ideal.annihilator_quotient]
          exact le_sup_left.trans hPJQ)
      · exact Module.mem_support_iff_of_finite.mpr (by
          rw [Ideal.annihilator_quotient]
          exact le_sup_right.trans hPJQ)
    exact (eq_maximalIdeal (isMaximal_of_mem_support_of_isFiniteLength _
      (Module.length_ne_top_iff.mp hfin) _ hmem)).ge



/-- 有限な Krull 次元は自然数である。 -/
theorem exists_nat_ringKrullDim_eq (S : Type*) [CommRing S] [FiniteRingKrullDim S] :
    ∃ n : ℕ, ringKrullDim S = n := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := S))
  have hdt : d ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := S)
    rw [← hd, h]
    rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hdt
  exact ⟨n, hd.symm.trans (congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) hn.symm)⟩

/-- 有限次元の整域で、商の次元が元の次元と等しいイデアルは零である。
非零元で割ると次元が真に下がることによる。 -/
theorem ideal_eq_bot_of_quotient_dim_eq {R : Type*} [CommRing R] [IsDomain R]
    [FiniteRingKrullDim R] (Q : Ideal R) (hQ : ringKrullDim (R ⧸ Q) = ringKrullDim R) :
    Q = ⊥ := by
  by_contra hne
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk Q)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hr0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  rw [hQ] at hdrop
  obtain ⟨n, hn⟩ := exists_nat_ringKrullDim_eq R
  rw [hn] at hdrop
  have : n + 1 ≤ n := by exact_mod_cast hdrop
  omega

end SerrePositivity
