module

public import SerrePositivity.CommutativeAlgebra.CompletedDifferential
public import SerrePositivity.CommutativeAlgebra.FractionDifferential
public import SerrePositivity.CommutativeAlgebra.CohenGabber.Parameters

/-! # Cohen–Gabber 3：分離的な正規化（主定理）

概要（Cohen–Gabber の定理、同標数の場合）：標数 `p` の次元 `h` の完備 Noether 局所整域 `D` に対し、
剰余体 `k` 上の冪級数環 `A = k[[X_1, …, X_h]]` からの単射な有限準同型 `A → D` で、剰余体へ全射、
かつ分数体の拡大 `Frac D / Frac A` が分離的なものが存在する（`exists_cohen_gabber_normalization`）。
Kurano–Shimomoto, *An elementary proof of Cohen–Gabber theorem in the equal characteristic
p > 0 case*, Theorem 1.1（https://arxiv.org/abs/1510.03573）。
方針：微分パラメータ `y`（`CohenGabber/Parameters`）で正規化 `F : A → D`（`X_i ↦ y_i`）を作る。`D(y_i)` が
生成点で完備微分 `Ω̂_{D/k}` を張るので、全射な係数制限 `Ω̂_{D/k} → Ω_{D/A}` は生成点で零。よって
`Frac D ⊗ Ω_{D/A} = 0` で、有限拡大の分離性の判定（`FractionDifferential`）から分離的。
規約：分数体の間の代数構造は Mathlib の `FractionRing.liftAlgebra`。主定理は `A` を抽象的な正則完備局所環とし、
`k[[X]]` との同型と標準座標を添えて述べる。
形式冪級数環の正則性・完備性には Stacks Project, Remark 10.160.9（https://stacks.math.columbia.edu/tag/0323）を併用する。
使われ方：論文の補題 2.2（`Paper/Section2/NormalizationBase`）。Mathlib への提出の最終目標。
-/

@[expose] public noncomputable section
namespace SerrePositivity

universe u
open scoped TensorProduct
open IsLocalRing


/-- 完備微分を変数の像の微分が張れば、同じ有限冪級数評価の分数体拡大は分離的。 -/
theorem isSeparable_powerSeries_fractionMap_of_completed_differential_span
    {k D : Type u} [Field k] [CommRing D] [IsDomain D] [Algebra k D]
    [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
    {σ : Type*} (F : MvPowerSeries σ k →+* D)
    (hF : Function.Injective F) (hfin : F.Finite)
    (hC : ∀ a, F (MvPowerSeries.C a) = algebraMap k D a)
    (y : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = y i)
    (hspan : Submodule.span (FractionRing D) (Set.range (fun i ↦
      baseChangeCompletedKaehlerDerivation (k := k) (FractionRing D) (maximalIdeal D) (y i))) = ⊤) :
    letI : Algebra (MvPowerSeries σ k) D := F.toAlgebra
    haveI : FaithfulSMul (MvPowerSeries σ k) D :=
      (faithfulSMul_iff_algebraMap_injective _ D).mpr hF
    letI := FractionRing.liftAlgebra (MvPowerSeries σ k) (FractionRing D)
    Algebra.IsSeparable (FractionRing (MvPowerSeries σ k)) (FractionRing D) := by
  let A := MvPowerSeries σ k
  let : Algebra A D := F.toAlgebra
  let : Module A D := @Algebra.toModule _ _ _ _ F.toAlgebra
  let : Module.Finite A D := hfin
  let : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq (fun a ↦ (hC a).symm)
  let g := completedDifferentialRestriction (R := A) (maximalIdeal D) le_rfl k
  let f := g.baseChange (FractionRing D)
  have hf : Function.Surjective f := LinearMap.baseChange_surjective (FractionRing D)
    (completedDifferentialRestriction_surjective (R := A) (maximalIdeal D) le_rfl k)
  have hfzero : f = 0 := by
    apply LinearMap.ext_on_range hspan
    intro i
    change (1 : FractionRing D) ⊗ₜ[D]
      g (AdicCompletion.of (maximalIdeal D) _ (KaehlerDifferential.D k D (y i))) = 0
    rw [completedDifferentialRestriction_D]
    have hy : KaehlerDifferential.D A D (y i) = 0 := by
      rw [← hX i]
      exact (KaehlerDifferential.D A D).map_algebraMap (MvPowerSeries.X i)
    rw [hy, TensorProduct.tmul_zero]
  let : Subsingleton (FractionRing D ⊗[D] KaehlerDifferential A D) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨v, rfl⟩ := hf x
    rw [hfzero, LinearMap.zero_apply]
  have : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hF
  exact (isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero' A D).mpr
    (Module.finrank_zero_of_subsingleton)

/-- 体の場合を含めて、係数切断と生成点の完備微分を張るパラメータを選ぶ。 -/
theorem exists_coefficient_section_differential_span
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (ψ : ResidueField D →+* D) (y : Fin h → D),
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      (∀ i, y i ∈ maximalIdeal D) ∧
      (Ideal.span (Set.range y)).radical = maximalIdeal D ∧
      letI : Algebra (ResidueField D) D := ψ.toAlgebra
      Submodule.span (FractionRing D) (Set.range (fun i ↦
        baseChangeCompletedKaehlerDerivation (k := ResidueField D)
          (FractionRing D) (maximalIdeal D) (y i))) = ⊤ := by
  classical
  by_cases hm : maximalIdeal D = ⊥
  · obtain ⟨φ, τ, _, hφ, hτ, _, _, _, _, _⟩ :=
      exists_equalCharacteristic_finite_normalization D hdim p
    let : Algebra (ResidueField D) D := φ.toAlgebra
    have hτm : ∀ i, τ i ∈ maximalIdeal D := by
      intro i
      rw [← hτ.2]
      exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
    have hinj : Function.Injective (residue D) :=
      (RingHom.injective_iff_ker_eq_bot (residue D)).mpr (by rw [ker_residue, hm])
    have hsurj : Function.Surjective (algebraMap (ResidueField D) D) := by
      intro d
      refine ⟨residue D d, hinj ?_⟩
      exact RingHom.congr_fun hφ (residue D d)
    let : Subsingleton (KaehlerDifferential (ResidueField D) D) :=
      KaehlerDifferential.subsingleton_of_surjective (ResidueField D) D hsurj
    let : Subsingleton (AdicCompletion (maximalIdeal D)
        (KaehlerDifferential (ResidueField D) D)) := by
      constructor
      intro x y
      ext n
      exact Subsingleton.elim _ _
    let : Subsingleton (FractionRing D ⊗[D] AdicCompletion (maximalIdeal D)
        (KaehlerDifferential (ResidueField D) D)) := inferInstance
    exact ⟨φ, τ, hφ, hτm, hτ.2, Subsingleton.elim _ _⟩
  · obtain ⟨ψ, y, hψ, hym, hyprim, B, hB⟩ :=
      exists_coefficient_section_differential_parameters D hdim p hm
    refine ⟨ψ, y, hψ, hym, hyprim, ?_⟩
    let : Algebra (ResidueField D) D := ψ.toAlgebra
    simp_rw [← hB]
    exact B.span_eq

/-- 同じ実際の冪級数評価に単射性・有限性・分離性を供給する。 -/
theorem exists_cohen_gabber_powerSeries_map
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (F : MvPowerSeries (Fin h) (ResidueField D) →+* D) (hF : Function.Injective F),
      F.Finite ∧ Function.Surjective ((residue D).comp F) ∧
      letI : Algebra (MvPowerSeries (Fin h) (ResidueField D)) D := F.toAlgebra
      haveI : FaithfulSMul (MvPowerSeries (Fin h) (ResidueField D)) D :=
        (faithfulSMul_iff_algebraMap_injective _ D).mpr hF
      letI := FractionRing.liftAlgebra (MvPowerSeries (Fin h) (ResidueField D)) (FractionRing D)
      Algebra.IsSeparable (FractionRing (MvPowerSeries (Fin h) (ResidueField D)))
        (FractionRing D) := by
  obtain ⟨ψ, y, hψ, hym, hyprim, hspan⟩ := exists_coefficient_section_differential_span D hdim p
  let : Algebra (ResidueField D) D := ψ.toAlgebra
  have hres : Function.Surjective ((residue D).comp ψ) := by
    rw [hψ]
    exact Function.surjective_id
  obtain ⟨F, hF, hfin, hresF, hC, hX⟩ :=
    exists_injective_finite_powerSeries_map_of_parameters ψ hres hdim y hym hyprim
  have hsep := isSeparable_powerSeries_fractionMap_of_completed_differential_span
    F hF hfin hC y hX hspan
  exact ⟨F, hF, hfin, hresF, hsep⟩

/-- Cohen–Gabber正規化の整域版。任意剰余体、空変数を含む。 -/
theorem exists_cohen_gabber_normalization
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧
      (∃ (_ : Algebra (FractionRing A) (FractionRing D))
        (_ : IsScalarTower A (FractionRing A) (FractionRing D)),
        Algebra.IsSeparable (FractionRing A) (FractionRing D)) ∧
      ∃ (t : Fin h → A) (e : A ≃+* MvPowerSeries (Fin h) (ResidueField D)),
        Ideal.span (Set.range t) = maximalIdeal A ∧
        ∀ i, e (t i) = MvPowerSeries.X i := by
  obtain ⟨F, hF, hfin, hresF, hsep⟩ := exists_cohen_gabber_powerSeries_map D hdim p
  let k := ResidueField D
  let A := MvPowerSeries (Fin h) k
  let : IsRegularLocalRing A := isRegularLocalRing_mvPowerSeries_fin k h
  let : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  let : IsAdicComplete (maximalIdeal A) A := isAdicComplete_powerSeries_maximalIdeal (Fin h) k
  let : Algebra A D := F.toAlgebra
  have : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hF
  let : Algebra (FractionRing A) (FractionRing D) := FractionRing.liftAlgebra A _
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hF, hfin, hresF, ⟨inferInstance, inferInstance, hsep⟩,
    MvPowerSeries.X, RingEquiv.refl A, ?_, fun _ ↦ rfl⟩
  rw [powerSeries_maximalIdeal_eq, maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq]

end SerrePositivity
