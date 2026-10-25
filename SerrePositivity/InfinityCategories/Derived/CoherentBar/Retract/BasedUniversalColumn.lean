module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedColumnAction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedUniversalCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ShiftUnitCancellation
/-!
概要：普遍 PInfty 係数から作る実 bar の退化列は零である。
方針：係数押出しの比較へ退化消滅を代入し、全 Hom でシフト単位を消去する。
規約：実安定作用素との一致は別に証明し、ここでは普遍係数の列だけを扱う。
使われ方：正規化比較から実退化列の消去を導くための係数側の入口。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarBasedUniversalColumn_comp_degeneracy_zero {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarBasedColumnAction R D F (n + 1) (I.σ j s)
        (dgCoherentBarBasedUniversalCoefficients R (n + 1)))
      (dgCoherentBarBasedBlock R D F (SimplexCategory.σ j) (by
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
      (by omega : ((n : ℤ) - ((n + 1 : ℕ) : ℤ)) +
        (((n + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) = (n : ℤ) - ((n + 1 : ℕ) : ℤ)) = 0 := by
  have h := dgCoherentBarBasedColumnAction_push R D F (SimplexCategory.σ j)
    (by simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s
    (dgCoherentBarBasedUniversalCoefficients R (n + 1))
  exact h.trans (by rw [dgCoherentBarBasedUniversalCoefficients_degeneracy, map_zero])

lemma dgCoherentBarBasedUniversalColumn_degeneracy_zero {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) :
    dgCoherentBarBasedColumnAction R D F (n + 1) (I.σ j s)
      (dgCoherentBarBasedUniversalCoefficients R (n + 1)) = 0 := by
  have hsource := dgCoherentBarSource_based_map R D F (SimplexCategory.σ j)
    (by simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s
  have htarget : ForgetEnrichment.to (Complex R)
      (dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩) =
      shiftModule ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n, s⟩) :=
    congrArg (shiftModule ((n + 1 : ℕ) : ℤ)) hsource
  exact dgBarRetractShiftUnit_transport_precompose_zero R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
    (dgCoherentBarSource R D F ⟨n, s⟩)
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) htarget
    (dgCoherentBarBasedBlock R D F (SimplexCategory.σ j) (by
      simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
    (dgCoherentBarBasedBlock_heq R D F (SimplexCategory.σ j) (by
      simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
    (dgCoherentBarBasedColumnAction R D F (n + 1) (I.σ j s)
      (dgCoherentBarBasedUniversalCoefficients R (n + 1))) (by omega)
    (dgCoherentBarBasedUniversalColumn_comp_degeneracy_zero R D F s j)

lemma dgCoherentBarBasedUniversalColumn_zero_of_degenerate {n : ℕ}
    (s : I _⦋n⦌) (hs : s ∈ I.degenerate n) :
    dgCoherentBarBasedColumnAction R D F n s
      (dgCoherentBarBasedUniversalCoefficients R n) = 0 := by
  cases n with
  | zero => simp only [I.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    have h := Set.mem_iUnion.mp ((Set.ext_iff.mp I.degenerate_eq_iUnion_range_σ s).mp hs)
    obtain ⟨j, t, ht⟩ := h
    cases ht
    exact dgCoherentBarBasedUniversalColumn_degeneracy_zero R D F t j

end SerrePositivity.InfinityCategories
