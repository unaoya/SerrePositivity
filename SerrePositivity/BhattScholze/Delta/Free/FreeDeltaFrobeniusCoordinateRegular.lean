module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaFrobeniusCoordinateResidueFlat
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-! # 自由δ Frobeniusの指定変数に沿う正則対

自由整数δ環に限る入力。一般perfectoid環のp正則性は要求しない。
通常の正則対と、完備化後の完全忠実平坦性は区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open scoped Pointwise
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
local notation "L₀" => FreeDeltaRing σ
local notation "R₀" => ModP L₀ p

/-- 自由整数δ環の指定変数のmod p像は正則。 -/
theorem freeDeltaCoordinate_modP_isSMulRegular (s : σ) :
    IsSMulRegular R₀ (Ideal.Quotient.mk (Ideal.span {(p : L₀)})
      (MvPolynomial.X (s, 0))) := by
  intro x y hxy
  apply (freeDeltaModPEquiv p σ).injective
  apply (MvPolynomial.isRegular_X (R := ZMod p) (n := (s, 0))).left
  have h := congrArg (freeDeltaModPEquiv p σ) hxy
  simpa only [smul_eq_mul, map_mul, freeDeltaModPEquiv_mk,
    freeDeltaModPMap, MvPolynomial.map_X] using h

/-- 自由整数δ環のφ(z)のmod p像も正則。 -/
theorem freeDeltaFrobeniusCoordinate_modP_isSMulRegular (s : σ) :
    IsSMulRegular R₀ (Ideal.Quotient.mk (Ideal.span {(p : L₀)})
      (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0)))) := by
  rw [freeDeltaFrobeniusCoordinate_mod_p]
  exact (freeDeltaCoordinate_modP_isSMulRegular p σ s).pow p

/-- 源の指定変数とpは自由整数δ環上の弱正則対。 -/
theorem freeDeltaCoordinate_pair_isWeaklyRegular (s : σ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ [(p : L₀), MvPolynomial.X (s, 0)] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨freeDeltaRing_p_mul_injective p σ, ?_⟩
  change IsSMulRegular (L₀ ⧸ ((p : L₀) • ⊤ : Submodule L₀ L₀)) _
  let e := Submodule.quotEquivOfEq
    ((p : L₀) • (⊤ : Submodule L₀ L₀))
    (Ideal.span {(p : L₀)} : Submodule L₀ L₀)
    (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
  apply (e.isSMulRegular_congr _).mpr
  exact (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp
    (freeDeltaCoordinate_modP_isSMulRegular p σ s)

/-- 対象のφ(z)とpも自由整数δ環上の弱正則対。 -/
theorem freeDeltaFrobeniusCoordinate_pair_isWeaklyRegular (s : σ) :
    RingTheory.Sequence.IsWeaklyRegular L₀
      [(p : L₀), freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨freeDeltaRing_p_mul_injective p σ, ?_⟩
  change IsSMulRegular (L₀ ⧸ ((p : L₀) • ⊤ : Submodule L₀ L₀)) _
  let e := Submodule.quotEquivOfEq
    ((p : L₀) • (⊤ : Submodule L₀ L₀))
    (Ideal.span {(p : L₀)} : Submodule L₀ L₀)
    (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
  apply (e.isSMulRegular_congr _).mpr
  exact (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp
    (freeDeltaFrobeniusCoordinate_modP_isSMulRegular p σ s)

/-- 源の実正則対のKoszul複体は通常商の分解。 -/
theorem freeDeltaCoordinate_pair_isKoszulResolution (s : σ) :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin 2 ↦ if i = 0 then (p : L₀) else MvPolynomial.X (s, 0)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa [List.ofFn_succ] using freeDeltaCoordinate_pair_isWeaklyRegular p σ s

/-- 対象の実正則対のKoszul複体も通常商の分解。 -/
theorem freeDeltaFrobeniusCoordinate_pair_isKoszulResolution (s : σ) :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin 2 ↦ if i = 0 then (p : L₀)
        else freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa [List.ofFn_succ] using freeDeltaFrobeniusCoordinate_pair_isWeaklyRegular p σ s

/-- 実Frobeniusに沿うL/(p,z)の全高次Torは零。
任意の(p,z)零化加群に対する完全平坦性の判定とは区別する。 -/
theorem freeDeltaFrobeniusCoordinate_residue_torAlg_subsingleton
    (s : σ) (i : ℕ) (hi : 0 < i) :
    Subsingleton (SerrePositivity.TorAlg (freeDeltaFrobenius p σ) i
      (L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.X (s, 0)})) := by
  let g : Fin 2 → L₀ := fun j ↦ if j = 0 then p else MvPolynomial.X (s, 0)
  have hg : freeDeltaFrobenius p σ ∘ g =
      (fun j : Fin 2 ↦ if j = 0 then (p : L₀)
        else freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))) := by
    funext j
    simp only [Function.comp_apply, g]
    split <;> simp_all
  have hz : CategoryTheory.Limits.IsZero
      ((SerrePositivity.koszulComplex (freeDeltaFrobenius p σ ∘ g)).homology (-(i : ℤ))) := by
    rw [hg]
    exact (freeDeltaFrobeniusCoordinate_pair_isKoszulResolution p σ s).isZero _ (by omega)
  have : Subsingleton (SerrePositivity.koszulHomologySelf
      (freeDeltaFrobenius p σ ∘ g) i) := ModuleCat.subsingleton_of_isZero hz
  have ht : Subsingleton (SerrePositivity.TorAlg (freeDeltaFrobenius p σ) i
      (L₀ ⧸ Ideal.span (Set.range g))) :=
    (SerrePositivity.torAlgKoszulEquiv (freeDeltaFrobenius p σ) g
      (freeDeltaCoordinate_pair_isKoszulResolution p σ s) i).injective.subsingleton
  have hr : Set.range g = {(p : L₀), MvPolynomial.X (s, 0)} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [g]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [g]⟩
      · exact ⟨1, by simp [g]⟩
  rw [hr] at ht
  exact ht

end SerrePositivity.BhattScholze
