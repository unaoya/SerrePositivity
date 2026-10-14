module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesAdicTopology
public import SerrePositivity.CommutativeAlgebra.PowerSeriesContinuousDifferential
public import SerrePositivity.CommutativeAlgebra.AdicDerivationContinuity

/-! # 変数イデアル進位相での連続導分

離散係数・有限変数で位相の一致を実際に適用する。
一般の位相的加群への入口では T2 性と連続な作用を明示する。
分離加群への入口では、代数的分離性から T2 性と導分の連続性を実際に供給する。
-/

@[expose] public section
namespace SerrePositivity
open scoped MvPowerSeries.WithPiTopology

variable {σ R M : Type*} [Finite σ] [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
  [IsScalarTower R (MvPowerSeries σ R) M] [TopologicalSpace M] [T2Space M]

omit [IsScalarTower R (MvPowerSeries σ R) M] in
/-- 変数イデアル進位相で連続な導分にも、変数の像による一意性が適用できる。 -/
theorem variables_adic_powerSeries_derivation_ext
    (δ₁ δ₂ : Derivation R (MvPowerSeries σ R) M)
    (h₁ : @Continuous (MvPowerSeries σ R) M
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicTopology inferInstance δ₁)
    (h₂ : @Continuous (MvPowerSeries σ R) M
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicTopology inferInstance δ₂)
    (hX : ∀ i, δ₁ (MvPowerSeries.X i) = δ₂ (MvPowerSeries.X i)) : δ₁ = δ₂ :=
  continuous_powerSeries_derivation_ext δ₁ δ₂
    ((powerSeries_continuous_iff_variables_adic δ₁).mpr h₁)
    ((powerSeries_continuous_iff_variables_adic δ₂).mpr h₂) hX

/-- 指定像を持つ導分は、変数イデアル進位相で連続に一意に構成できる。 -/
theorem existsUnique_variables_adic_powerSeriesDerivation [IsTopologicalAddGroup M]
    [ContinuousSMul (MvPowerSeries σ R) M] (a : σ → M) :
    ∃! δ : Derivation R (MvPowerSeries σ R) M,
      @Continuous (MvPowerSeries σ R) M
        (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicTopology inferInstance δ ∧
          ∀ i, δ (MvPowerSeries.X i) = a i := by
  simpa only [← powerSeries_continuous_iff_variables_adic] using
    existsUnique_continuous_powerSeriesDerivation (R := R) a

omit [TopologicalSpace M] [T2Space M] in
/-- 終域にも実際の変数イデアル進加群位相を入れる。
連続な加法・作用はMathlibから供給し、T2性だけを明示する。 -/
theorem existsUnique_adicModule_powerSeriesDerivation
    (hM : @T2Space M
      ((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicModuleTopology M))
    (a : σ → M) :
    ∃! δ : Derivation R (MvPowerSeries σ R) M,
      @Continuous (MvPowerSeries σ R) M
        (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicTopology
        ((Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).adicModuleTopology M) δ ∧
          ∀ i, δ (MvPowerSeries.X i) = a i := by
  let J := Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
  let : TopologicalSpace M := J.adicModuleTopology M
  let : T2Space M := hM
  let : IsTopologicalAddGroup M := by
    let : WithIdeal (MvPowerSeries σ R) := ⟨J⟩
    infer_instance
  have hs : @ContinuousSMul (MvPowerSeries σ R) M _ J.adicTopology inferInstance := by
    let : WithIdeal (MvPowerSeries σ R) := ⟨J⟩
    infer_instance
  let : ContinuousSMul (MvPowerSeries σ R) M := by
    have ht : (inferInstance : TopologicalSpace (MvPowerSeries σ R)) = J.adicTopology :=
      powerSeries_piTopology_isAdic_variables
    change @ContinuousSMul (MvPowerSeries σ R) M _
      (inferInstance : TopologicalSpace (MvPowerSeries σ R)) inferInstance
    rw [ht]
    exact hs
  exact existsUnique_variables_adic_powerSeriesDerivation (R := R) a

omit [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [T2Space M]
    [IsScalarTower R (MvPowerSeries σ R) M] in
/-- 代数的に分離な加群への通常の導分は、連続性を仮定せず変数の像で決まる。 -/
theorem powerSeries_derivation_ext_of_isHausdorff
    [IsHausdorff (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) M]
    (δ₁ δ₂ : Derivation R (MvPowerSeries σ R) M)
    (hX : ∀ i, δ₁ (MvPowerSeries.X i) = δ₂ (MvPowerSeries.X i)) : δ₁ = δ₂ := by
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let J := Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
  let : TopologicalSpace M := J.adicModuleTopology M
  let : T2Space M := t2Space_adicModule_of_isHausdorff J
  exact variables_adic_powerSeries_derivation_ext δ₁ δ₂
    (continuous_derivation_adic δ₁ J) (continuous_derivation_adic δ₂ J) hX

omit [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [T2Space M] in
/-- 分離加群には、指定像を持つ通常の導分が一意に存在する。完備性は不要。 -/
theorem existsUnique_powerSeriesDerivation_of_isHausdorff
    [IsHausdorff (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) M]
    (a : σ → M) :
    ∃! δ : Derivation R (MvPowerSeries σ R) M, ∀ i, δ (MvPowerSeries.X i) = a i := by
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let J := Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))
  obtain ⟨δ, hδ, _⟩ := existsUnique_adicModule_powerSeriesDerivation (R := R)
    (t2Space_adicModule_of_isHausdorff J) a
  refine ⟨δ, hδ.2, ?_⟩
  intro ε hε
  exact powerSeries_derivation_ext_of_isHausdorff ε δ
    (fun i ↦ (hε i).trans (hδ.2 i).symm)

end SerrePositivity
