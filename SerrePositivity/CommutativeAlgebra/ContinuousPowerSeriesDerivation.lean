module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Module.Basic

/-! # 冪級数環の連続導分

係数の積位相を明示する。一般の係数位相をイデアル進位相と同一視しない。
偏微分と多項式の稠密性には Mathlib の既存定理を用いる。
-/

@[expose] public section
namespace SerrePositivity
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

/-- 変数の指定像から、偏微分の有限和で実際の導分を作る。 -/
noncomputable def powerSeriesDerivation (a : σ → M) : Derivation R (MvPowerSeries σ R) M :=
  ∑ i, (LinearMap.toSpanSingleton (MvPowerSeries σ R) M (a i)).compDer
    (MvPowerSeries.pderiv (R := R) i)

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace M] in
theorem powerSeriesDerivation_apply (a : σ → M) (f : MvPowerSeries σ R) :
    powerSeriesDerivation (R := R) a f = ∑ i, MvPowerSeries.pderiv (R := R) i f • a i := by
  simp [powerSeriesDerivation]

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace M] in
@[simp] theorem powerSeriesDerivation_X (a : σ → M) (j : σ) :
    powerSeriesDerivation (R := R) a (MvPowerSeries.X j) = a j := by
  classical
  rw [powerSeriesDerivation_apply]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply]

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

end SerrePositivity
