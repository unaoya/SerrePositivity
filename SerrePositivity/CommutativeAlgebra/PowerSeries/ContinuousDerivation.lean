module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Module.Basic
public import SerrePositivity.RingTheory.Derivation
public import SerrePositivity.CommutativeAlgebra.Adic.Topology
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Derivation

/-! # 冪級数環の連続導分

概要：係数環 `R` に位相を入れ、冪級数環 `A = R[[X]]` に係数ごとの積位相を入れる。
- 形式偏微分は連続。T2 な位相加群への連続導分は変数の像で決まり、有限変数なら任意の像に対して存在する。
  連続導分のなす `A` 加群は `M^σ` と線形同型で、有限自由加群 `A^σ` からの連続な線形写像とも対応する。
- 任意の導分はイデアル進位相について連続（源と終域に同じイデアルの位相）。
- 係数が離散で変数が有限なら、積位相は変数イデアル進位相に等しい（`PowerSeries/Basic`）ので、
  変数進位相についても同じ一意性と存在が成り立つ。
方針：一意性は多項式の稠密性（Mathlib の `MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries`）、
存在は偏微分の和（`powerSeriesDerivation`）。連続性は導分がイデアル冪の次数を高々一つ下げることから。
規約：代数的な版（分離な加群への一意性）は位相を使わずに `PowerSeries/Derivation` で示す。
使われ方：現在の Cohen–Gabber の証明では使わない。冪級数環の完備微分を連続導分の表現として扱う一般論で、
Mathlib への提出候補（mathlib-upstream）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section PiTopology

open scoped MvPowerSeries.WithPiTopology

variable {σ R M : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
  [IsScalarTower R (MvPowerSeries σ R) M] [TopologicalSpace M]

/-- 形式偏微分は係数の積位相で連続。変数の有限性・標数の仮定は不要。 -/
theorem continuous_powerSeries_pderiv (i : σ) :
    Continuous (MvPowerSeries.pderiv (R := R) i) := by
  apply continuous_pi
  intro d
  change Continuous (fun f : MvPowerSeries σ R ↦
    MvPowerSeries.coeff d (MvPowerSeries.pderiv i f))
  simp only [MvPowerSeries.coeff_pderiv]
  exact (MvPowerSeries.WithPiTopology.continuous_coeff R
    (d + Finsupp.single i 1)).mul continuous_const

omit [IsTopologicalRing R] [IsScalarTower R (MvPowerSeries σ R) M] in
/-- 分離な終域への連続導分は変数の像で決まる。完備性・有限変数は不要。 -/
theorem continuous_powerSeries_derivation_ext [T2Space M]
    (δ₁ δ₂ : Derivation R (MvPowerSeries σ R) M)
    (h₁ : Continuous δ₁) (h₂ : Continuous δ₂)
    (hX : ∀ i, δ₁ (MvPowerSeries.X i) = δ₂ (MvPowerSeries.X i)) : δ₁ = δ₂ := by
  have hpoly : ∀ f : MvPolynomial σ R, δ₁ (f : MvPowerSeries σ R) = δ₂ f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.coe_C]
      change δ₁ (algebraMap R (MvPowerSeries σ R) r) = δ₂ (algebraMap R (MvPowerSeries σ R) r)
      rw [δ₁.map_algebraMap, δ₂.map_algebraMap]
    | add f g hf hg =>
      simpa only [MvPolynomial.coe_add, map_add] using congrArg₂ (· + ·) hf hg
    | mul_X f i hf =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, hf, hX]
  apply DFunLike.coe_injective
  exact MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer h₁ h₂ (funext hpoly)

variable [Fintype σ]

/-- 指定像からの導分の連続性は、偏微分と加群の連続な作用から確認する。 -/
theorem continuous_powerSeriesDerivation [IsTopologicalAddGroup M]
    [ContinuousSMul (MvPowerSeries σ R) M] (a : σ → M) :
    Continuous (powerSeriesDerivation (R := R) a) := by
  simp only [show (powerSeriesDerivation (R := R) a : MvPowerSeries σ R → M) =
      (fun f ↦ ∑ i, MvPowerSeries.pderiv (R := R) i f • a i) from
        funext (powerSeriesDerivation_apply a)]
  exact continuous_finsetSum _ (fun i _ ↦ (continuous_powerSeries_pderiv i).smul continuous_const)

omit [Fintype σ] in
/-- 有限変数の場合、指定像を持つ連続導分は存在して一意。 -/
theorem existsUnique_continuous_powerSeriesDerivation [Finite σ] [T2Space M]
    [IsTopologicalAddGroup M]
    [ContinuousSMul (MvPowerSeries σ R) M] (a : σ → M) :
    ∃! δ : Derivation R (MvPowerSeries σ R) M,
      Continuous δ ∧ ∀ i, δ (MvPowerSeries.X i) = a i := by
  classical
  let := Fintype.ofFinite σ
  refine ⟨powerSeriesDerivation (R := R) a,
    ⟨continuous_powerSeriesDerivation (R := R) a, powerSeriesDerivation_X a⟩, ?_⟩
  intro δ hδ
  exact continuous_powerSeries_derivation_ext δ _ hδ.1 (continuous_powerSeriesDerivation (R := R) a)
    (fun i ↦ (hδ.2 i).trans (powerSeriesDerivation_X a i).symm)

variable [IsTopologicalAddGroup M] [ContinuousSMul (MvPowerSeries σ R) M]

omit [Fintype σ] [IsTopologicalRing R] in
/-- 連続導分は通常の導分加群の部分加群をなす。変数の有限性は不要。 -/
def continuousPowerSeriesDerivations :
    Submodule (MvPowerSeries σ R) (Derivation R (MvPowerSeries σ R) M) where
  carrier := {δ | Continuous δ}
  zero_mem' := continuous_const
  add_mem' := fun hδ hε ↦ hδ.add hε
  smul_mem' := fun _ _ hδ ↦ continuous_const.smul hδ

variable [T2Space M]

/-- 連続導分の加群は、変数の像の加群と線形同型になる。 -/
noncomputable def continuousPowerSeriesDerivationEquiv :
    continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M) ≃ₗ[MvPowerSeries σ R] (σ → M) where
  toFun δ i := δ.val (MvPowerSeries.X i)
  invFun a := ⟨powerSeriesDerivation (R := R) a, continuous_powerSeriesDerivation (R := R) a⟩
  left_inv δ := by
    apply Subtype.ext
    apply continuous_powerSeries_derivation_ext _ _
      (continuous_powerSeriesDerivation _) δ.property
    intro i
    exact powerSeriesDerivation_X _ i
  right_inv a := funext (powerSeriesDerivation_X a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem continuousPowerSeriesDerivationEquiv_apply
    (δ : continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M)) (i : σ) :
    continuousPowerSeriesDerivationEquiv δ i = δ.val (MvPowerSeries.X i) := rfl

@[simp] theorem continuousPowerSeriesDerivationEquiv_symm_apply (a : σ → M) :
    (continuousPowerSeriesDerivationEquiv (R := R)).symm a =
      ⟨powerSeriesDerivation (R := R) a, continuous_powerSeriesDerivation (R := R) a⟩ := rfl

end PiTopology

section Adic

open Topology

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M]

/-- 任意の導分は、源と終域の同じイデアルによる位相で連続。 -/
theorem continuous_derivation_adic (δ : Derivation R S M) (I : Ideal S) :
    @Continuous S M I.adicTopology (I.adicModuleTopology M) δ := by
  let : WithIdeal S := ⟨I⟩
  let : TopologicalSpace M := I.adicModuleTopology M
  let : IsTopologicalAddGroup M := by infer_instance
  apply continuous_of_tendsto_nhds_zero δ.toAddMonoidHom
  rw [I.hasBasis_nhds_zero_adic.tendsto_iff (hasBasis_nhds_zero_adicModule I)]
  intro n _
  refine ⟨n + 1, trivial, ?_⟩
  intro x hx
  exact derivation_mem_pow_smul δ I n hx

end Adic

section VariablesAdic

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

end VariablesAdic

section Representation

open scoped MvPowerSeries.WithPiTopology

variable {σ R : Type*} [Fintype σ] [CommRing R]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_powerSeriesContinuousDifferential :
    Continuous (powerSeriesContinuousDifferential (σ := σ) (R := R)) := by
  apply continuous_pi
  intro i
  simpa only [powerSeriesContinuousDifferential_apply] using
    continuous_powerSeries_pderiv (R := R) i

variable {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
  [IsScalarTower R (MvPowerSeries σ R) M] [TopologicalSpace M] [T2Space M]
  [IsTopologicalAddGroup M] [ContinuousSMul (MvPowerSeries σ R) M]

/-- 連続導分と有限自由加群からの線形写像との実際の線形同型。 -/
noncomputable def powerSeriesContinuousDifferentialLiftEquiv :
    continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M) ≃ₗ[MvPowerSeries σ R]
      ((σ → MvPowerSeries σ R) →ₗ[MvPowerSeries σ R] M) :=
  continuousPowerSeriesDerivationEquiv.trans (Module.piEquiv σ (MvPowerSeries σ R) M)

/-- 対応する線形写像は、自由加群への導分を元の連続導分へ送る。 -/
theorem powerSeriesContinuousDifferentialLiftEquiv_comp
    (δ : continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M)) (f : MvPowerSeries σ R) :
    powerSeriesContinuousDifferentialLiftEquiv δ (powerSeriesContinuousDifferential f) =
      δ.val f := by
  change Module.piEquiv σ (MvPowerSeries σ R) M (fun i ↦ δ.val (MvPowerSeries.X i))
    (powerSeriesContinuousDifferential f) = _
  rw [Module.piEquiv_apply_apply]
  simp only [powerSeriesContinuousDifferential_apply]
  rw [← powerSeriesDerivation_apply]
  have he : powerSeriesDerivation (R := R) (fun i ↦ δ.val (MvPowerSeries.X i)) = δ.val :=
    continuous_powerSeries_derivation_ext _ _ (continuous_powerSeriesDerivation _) δ.property
      (fun i ↦ powerSeriesDerivation_X _ i)
  exact congrArg (fun d : Derivation R (MvPowerSeries σ R) M ↦ d f) he

/-- 表現する線形写像自身も連続である。有限自由性と連続な係数作用を使う。 -/
theorem continuous_powerSeriesContinuousDifferentialLiftEquiv
    (δ : continuousPowerSeriesDerivations (σ := σ) (R := R) (M := M)) :
    Continuous (powerSeriesContinuousDifferentialLiftEquiv δ) := by
  change Continuous (Module.piEquiv σ (MvPowerSeries σ R) M
    (fun i ↦ δ.val (MvPowerSeries.X i)))
  have he : (Module.piEquiv σ (MvPowerSeries σ R) M
      (fun i ↦ δ.val (MvPowerSeries.X i)) : (σ → MvPowerSeries σ R) → M) =
      (fun v ↦ ∑ i, v i • δ.val (MvPowerSeries.X i)) :=
    funext (Module.piEquiv_apply_apply _ _ _ _)
  rw [he]
  exact continuous_finsetSum _ (fun i _ ↦ (continuous_apply i).smul continuous_const)

end Representation

end SerrePositivity
