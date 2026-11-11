module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumnAction
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedUniversalCoefficients
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ShiftUnitCancellation
/-!
概要：普遍 PInfty 係数から作る実 bar の退化列は零である。
方針：係数押出しの比較へ退化消滅を代入し、全 Hom でシフト単位を消去する。
規約：実安定作用素との一致は別に証明し、ここでは普遍係数の列だけを扱う。
使われ方：正規化比較から実退化列の消去を導くための係数側の入口。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarBasedUniversalColumn_comp_degeneracy_zero {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F (n + 1) (I.σ j s)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.σ j) (by
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
      (by omega : ((n : ℤ) - ((n + 1 : ℕ) : ℤ)) +
        (((n + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) = (n : ℤ) - ((n + 1 : ℕ) : ℤ)) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction_push R D F (SimplexCategory.σ j)
    (by simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R (n + 1))
  exact h.trans (by rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients_degeneracy, map_zero])

lemma dgCoherentBarBasedUniversalColumn_degeneracy_zero {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F (n + 1) (I.σ j s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R (n + 1)) = 0 := by
  have hsource := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarSource_based_map R D F (SimplexCategory.σ j)
    (by simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s
  have htarget : ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩) =
      shiftModule ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩) :=
    congrArg (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ)) hsource
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetractShiftUnit_transport_precompose_zero R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) htarget
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.σ j) (by
      simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock_heq R D F (SimplexCategory.σ j) (by
      simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F (n + 1) (I.σ j s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R (n + 1))) (by omega)
    (dgCoherentBarBasedUniversalColumn_comp_degeneracy_zero R D F s j)

lemma dgCoherentBarBasedUniversalColumn_zero_of_degenerate {n : ℕ}
    (s : I _⦋n⦌) (hs : s ∈ I.degenerate n) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R n) = 0 := by
  cases n with
  | zero => simp only [I.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    have h := Set.mem_iUnion.mp ((Set.ext_iff.mp I.degenerate_eq_iUnion_range_σ s).mp hs)
    obtain ⟨j, t, ht⟩ := h
    cases ht
    exact dgCoherentBarBasedUniversalColumn_degeneracy_zero R D F t j

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
