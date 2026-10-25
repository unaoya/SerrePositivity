module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageHomologyDescent

/-!
概要：filtered coherent bar のホモロジーは零単体次元の段階から生成される。
方針：実長完全列による一段下降を有限 support の上限について帰納する。
規約：高次 HA 項を残した実複体を扱い、有界性や形式的収束を仮定しない。
使われ方：最終ホモロジーを一次微分の余核として同定する。
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

lemma dgCoherentBarStageHomology_from_zero (x : D) (q : ℤ) (n : ℕ)
    (a : (dgCoherentBarNormalizedStageComplex R D G x n).homology q) :
    ∃ b : (dgCoherentBarNormalizedStageComplex R D G x 0).homology q,
      HomologicalComplex.homologyMap (dgCoherentBarNormalizedStageInclusion R D G x 0) q b =
      HomologicalComplex.homologyMap (dgCoherentBarNormalizedStageInclusion R D G x n) q a := by
  induction n with
  | zero => exact ⟨a, rfl⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := dgCoherentBarStageHomology_descent R D G x q n a
    have h : HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageInclusion R D G x n) q b =
      HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageInclusion R D G x (n + 1)) q a := by
      have h := congrArg (fun z => HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageInclusion R D G x (n + 2)) q z) hb
      simpa only [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
        dgCoherentBarNormalizedStageMap_inclusion] using! h
    obtain ⟨c, hc⟩ := ih b
    exact ⟨c, hc.trans h⟩

lemma dgCoherentBarZeroStageHomology_surjective (x : D) (q : ℤ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (dgCoherentBarNormalizedStageInclusion R D G x 0) q) := by
  intro a
  obtain ⟨n, b, hb⟩ := dgCoherentBarStageHomology_exhaustive R D G x q a
  obtain ⟨c, hc⟩ := dgCoherentBarStageHomology_from_zero R D G x q n b
  exact ⟨c, hc.trans hb⟩

end SerrePositivity.InfinityCategories
