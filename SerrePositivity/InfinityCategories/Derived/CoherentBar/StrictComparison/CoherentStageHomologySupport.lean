module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexHomologyClassBoundary
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStages

/-!
概要：実正規化 bar の全ホモロジー類は有限段階から来る。
方針：cycle の有限 support を持ち上げ、次数ごとの包含の単射性で閉性を反映する。
規約：全 HA 成分を含む実微分と非有界整数次数を使う。
使われ方：一次完全性による有限段階からの下降。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarStageInclusion_injective (x : D) (n : ℕ) (q : ℤ) :
    Function.Injective ((dgCoherentBarNormalizedStageInclusion R D G x n).f q) :=
  Subtype.val_injective

@[reassoc]
lemma dgCoherentBarStageMap_comp (x : D) {l n m : ℕ} (h₁ : l ≤ n) (h₂ : n ≤ m) :
    dgCoherentBarNormalizedStageMap R D G x h₁ ≫
      dgCoherentBarNormalizedStageMap R D G x h₂ =
        dgCoherentBarNormalizedStageMap R D G x (h₁.trans h₂) := by
  ext q z
  rfl

lemma dgCoherentBarStageHomology_exhaustive (x : D) (q : ℤ)
    (a : ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q) :
    ∃ (n : ℕ) (b : (dgCoherentBarNormalizedStageComplex R D G x n).homology q),
      HomologicalComplex.homologyMap (dgCoherentBarNormalizedStageInclusion R D G x n) q b = a := by
  let K := (dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)
  obtain ⟨z, hz, rfl⟩ := dgComplexHomologyClass_surjective R K q a
  obtain ⟨n, b, hb⟩ := dgCoherentBarNormalizedStages_exhaustive R D G x q z
  let f := dgCoherentBarNormalizedStageInclusion R D G x n
  have hbz : (dgCoherentBarNormalizedStageComplex R D G x n).d q (q + 1) b = 0 := by
    apply dgCoherentBarStageInclusion_injective R D G x n (q + 1)
    have h := ConcreteCategory.congr_hom (f.comm q (q + 1)) b
    change K.d q (q + 1) (f.f q b) =
      f.f (q + 1) ((dgCoherentBarNormalizedStageComplex R D G x n).d q (q + 1) b) at h
    rw [hb, hz] at h
    simpa only [map_zero] using! h.symm
  refine ⟨n, dgComplexHomologyClass R _ q b hbz, ?_⟩
  have hb' : K.d q (q + 1) (f.f q b) = 0 := by rw [hb]; exact hz
  change f.f q b = z at hb
  have h := dgComplexHomologyClass_map R f q b hbz hb'
  simpa only [hb] using! h

end SerrePositivity.InfinityCategories
