module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageFiniteKernel
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageKernelDescent

/-!
概要：零段階から実 bar へのホモロジー射の核は、最初の連結射の像である。
方針：境界の有限 support と隣接二段の核の下降を組み合わせる。
規約：全高次 HA を保持した実長完全列を使う。
使われ方：実 bar のホモロジーを一次微分の余核へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarZeroStageHomology_kernel_at_one (x : D) (p : ℤ)
    (a : (dgCoherentBarNormalizedStageComplex R D G x 0).homology (p + 1))
    (m : ℕ) :
    HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageMap R D G x (Nat.zero_le m)) (p + 1) a = 0 →
    HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageMap R D G x (show 0 ≤ 1 by omega)) (p + 1) a = 0 := by
  induction m with
  | zero =>
    intro ha
    have h := congrArg (fun z => HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageMap R D G x (show 0 ≤ 1 by omega)) (p + 1) z) ha
    simpa only [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
      dgCoherentBarStageMap_comp, map_zero] using! h
  | succ m ih =>
    cases m with
    | zero => exact fun h => h
    | succ n =>
      intro ha
      let b := HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageMap R D G x (Nat.zero_le n)) (p + 1) a
      have hb : HomologicalComplex.homologyMap
          (dgCoherentBarNormalizedStageMap R D G x (show n ≤ n + 2 by omega)) (p + 1) b = 0 := by
        dsimp only [b]
        rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
          dgCoherentBarStageMap_comp]
        exact ha
      have h := dgCoherentBarStageHomology_kernel_descent R D G x p n b hb
      apply ih
      simpa only [b, ← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
        dgCoherentBarStageMap_comp] using! h

lemma dgCoherentBarZeroStageHomology_kernel (x : D) (p : ℤ)
    (a : (dgCoherentBarNormalizedStageComplex R D G x 0).homology (p + 1))
    (ha : HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1) a = 0) :
    ∃ b : ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G 1)).homology p,
      (dgCoherentBarLayerSequence_shortExact R D G x 0).δ p (p + 1) (by simp) b = a := by
  obtain ⟨m, hm⟩ := dgCoherentBarZeroStageHomology_finiteKernel R D G x (p + 1) a ha
  have h := dgCoherentBarZeroStageHomology_kernel_at_one R D G x p a m hm
  exact (ShortComplex.moduleCat_exact_iff _).mp
    ((dgCoherentBarLayerSequence_shortExact R D G x 0).homology_exact₁ p (p + 1) (by simp)) a h

end SerrePositivity.InfinityCategories
