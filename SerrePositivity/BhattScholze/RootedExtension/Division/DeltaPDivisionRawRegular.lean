module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionFiniteStageRegular
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionUniversal
public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFrobeniusShift
public import SerrePositivity.BhattScholze.Delta.DeltaPrime
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # 一元rawδ p除算包のp正則性と旧ねじれ除去商との比較

有限実関係商の正則性をδ閉包へ移す。単元δ(p)とghost単射を明示する。
導来pushoutの離散性・完備化後のCFFとは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀
local notation "J₀" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal (p : A) a₀)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "K₀" => RingHom.ker (algebraMap B₀ (Localization.Away (j₀ (p : A))))
include hpA hg hv hy

/-- 有限段でのp正則性から、実δ閉包イデアルのp飽和性を得る。 -/
theorem deltaPDivisionRaw_relationIdeal_p_saturated (f : L₀) (hf : (p : L₀) * f ∈ J₀) :
    f ∈ J₀ := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations] at hf ⊢
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _
    (deltaDivisionFiniteRelationIdeal_mono D (p : A) a₀).directed_le).mp hf
  have hpN := deltaPDivisionFiniteStage_quotient_p_mul_injective (σ := σ) D y hpA hg v hv hy N
  have hz : Ideal.Quotient.mk (I₀ N) f = 0 := by
    apply hpN
    change (p : L₀ ⧸ I₀ N) * Ideal.Quotient.mk (I₀ N) f = (p : L₀ ⧸ I₀ N) * 0
    rw [mul_zero, ← map_natCast (Ideal.Quotient.mk (I₀ N)) p, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
  exact (le_iSup I₀ N) (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- 一元rawδ添加環A{φ(y)/p}そのものはp正則。 -/
theorem deltaPDivisionRaw_p_mul_injective :
    Function.Injective (fun x : B₀ ↦ (p : B₀) * x) := by
  let q := Ideal.Quotient.mk J₀
  intro x z hxz
  change (p : B₀) * x = (p : B₀) * z at hxz
  apply sub_eq_zero.mp
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (x - z)
  have hpf : q ((p : L₀) * f) = 0 := by
    rw [map_mul, map_natCast, hf, mul_sub, hxz, sub_self]
  have hm := deltaPDivisionRaw_relationIdeal_p_saturated (σ := σ) D y hpA hg v hv hy f
    (Ideal.Quotient.eq_zero_iff_mem.mp hpf)
  exact hf.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm)

omit hv in
/-- 源がp進完備なら、δ(p)の単元性を既存のJacobson根基判定から内部で供給できる。 -/
theorem deltaPDivisionRaw_p_mul_injective_of_adicComplete
    [IsAdicComplete (Ideal.span {(p : A)}) A] :
    Function.Injective (fun x : B₀ ↦ (p : B₀) * x) := by
  have hdist := D.isDistinguished_p
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))
  obtain ⟨w, hw⟩ := hdist
  exact deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg w hw hy

/-- 同じ仮定で、y^p/pのrawδ添加環もp正則。証明済み平行移動同型で移す。 -/
theorem deltaPDivisionRawPower_p_mul_injective :
    Function.Injective (fun x : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p) ↦
      (p : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p)) * x) := by
  let e := deltaPDivisionFrobeniusShiftEquiv D (fun _ : σ ↦ y)
  intro x z hxz
  change (p : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p)) * x =
    (p : DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ y ^ p)) * z at hxz
  apply e.symm.injective
  apply deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
  have h := congrArg e.symm hxz
  simpa only [map_mul, map_natCast] using h

/-- このrawδ包では旧p冪ねじれ、すなわちp局所化への核は既に零。 -/
theorem deltaPDivisionRaw_ker_away_eq_bot : K₀ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (j₀ (p : A))) (Localization.Away (j₀ (p : A))) x).mp hx
  obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (m : B₀) (j₀ (p : A))).mp m.property
  have hp : IsLeftRegular (j₀ (p : A)) := by
    intro z t hzt
    apply deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy
    simpa only [map_natCast (j₀) p] using hzt
  apply Ideal.mem_bot.mpr
  apply hp.pow N
  change (j₀ (p : A)) ^ N * x = (j₀ (p : A)) ^ N * 0
  rw [hN, hm, mul_zero]

/-- 旧pねじれのδ閉包も零であり、ここでは除去商で環を変えない。 -/
theorem deltaPDivisionRaw_torsion_deltaClosure_eq_bot : (E₀).deltaClosure K₀ = ⊥ := by
  have hK := deltaPDivisionRaw_ker_away_eq_bot (σ := σ) D y hpA hg v hv hy
  have hstable : (E₀).IsStable (⊥ : Ideal B₀) := by
    intro x hx
    rw [Ideal.mem_bot] at hx ⊢
    rw [hx, DeltaStructure.delta_zero]
  exact (congrArg (E₀).deltaClosure hK).trans ((E₀).deltaClosure_eq hstable)

/-- 一元rawδ包と既存旧ねじれ除去商を標準商射で比較する具体的同型。 -/
def deltaPDivisionRawTorsionEquiv : B₀ ≃+* DeltaDivisionTorsionQuotient D (p : A) a₀ :=
  (RingEquiv.quotientBot B₀).symm.trans (Ideal.quotEquivOfEq
    (deltaPDivisionRaw_torsion_deltaClosure_eq_bot (σ := σ) D y hpA hg v hv hy).symm)

/-- 同型は実際の旧ねじれ除去の標準商射。 -/
theorem deltaPDivisionRawTorsionEquiv_apply (x : B₀) :
    deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy x = Ideal.Quotient.mk _ x := by
  rw [deltaPDivisionRawTorsionEquiv, RingEquiv.trans_apply, RingEquiv.quotientBot_symm_mk,
    Ideal.quotEquivOfEq_mk]

/-- raw包と除去商の比較の両方向は既存δ構造と両立する。 -/
theorem deltaPDivisionRawTorsionEquiv_isDeltaHom :
    (E₀).IsDeltaHom (deltaDivisionTorsionStructure D (p : A) a₀)
        (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy).toRingHom ∧
      (deltaDivisionTorsionStructure D (p : A) a₀).IsDeltaHom E₀
        (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy).symm.toRingHom := by
  let e := deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy
  have hf : (E₀).IsDeltaHom (deltaDivisionTorsionStructure D (p : A) a₀) e.toRingHom := by
    intro x
    change e ((E₀).delta x) = (deltaDivisionTorsionStructure D (p : A) a₀).delta (e x)
    rw [deltaPDivisionRawTorsionEquiv_apply, deltaPDivisionRawTorsionEquiv_apply]
    exact ((E₀).isDeltaHom_quotient_mk _ ((E₀).isStable_deltaClosure _)) x
  refine ⟨hf, ?_⟩
  intro x
  apply e.injective
  change e (e.symm ((deltaDivisionTorsionStructure D (p : A) a₀).delta x)) =
    e ((E₀).delta (e.symm x))
  rw [RingEquiv.apply_symm_apply]
  have hfx : e ((E₀).delta (e.symm x)) =
      (deltaDivisionTorsionStructure D (p : A) a₀).delta (e (e.symm x)) := hf (e.symm x)
  rw [RingEquiv.apply_symm_apply] at hfx
  exact hfx.symm

/-- 比較同型は元の係数環からの実標準射を保つ。 -/
theorem deltaPDivisionRawTorsionEquiv_comp :
    (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy).toRingHom.comp j₀ =
      deltaDivisionTorsionMap D (p : A) a₀ := by
  ext x
  change deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hg v hv hy (j₀ x) = _
  rw [deltaPDivisionRawTorsionEquiv_apply]
  rfl

end SerrePositivity.BhattScholze
