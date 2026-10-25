module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerShortExact
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients

/-!
概要：実 coherent bar の零段階を零次元層へ同定する。
方針：零次元支持では層射影と包含が互いに逆であることを示す。
規約：実微分に関する複体同型を作る。
使われ方：最終ホモロジー比較の頂点側。
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

lemma dgCoherentBarZeroLayer_recover (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q 0) :
    (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G 0)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G 0) z) = z := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  let f := dgCoherentBarNormalizedProjection R D G ≫
    dgCoherentBarLayerProjection R D G 0 ≫ dgCoherentBarLayerInclusion R D G 0 -
      dgCoherentBarNormalizedProjection R D G
  have hf : ∀ s : dgCoherentBarIndex I, s.1 ≤ 0 →
      Sigma.ι (dgCoherentBarFamily R D G) s ≫ f = 0 := by
    intro s hs
    dsimp only [f]
    rw [Preadditive.comp_sub,
      dgCoherentBarLayerProjection_raw_ι_of_eq R D G 0 s (by omega), sub_self]
  have h := dgCoherentBarDegreeFiltration_annihilate R D G f x q 0 hf a ha
  change (moduleDegreeEvaluation R D x q).map f a = 0 at h
  change ((moduleDegreeEvaluation R D x q).map f).hom a = 0 at h
  simpa only [f, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_comp,
    ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.comp_apply, sub_eq_zero] using! h

lemma dgCoherentBarZeroStageToLayer_injective (x : D) (q : ℤ) :
    Function.Injective ((dgCoherentBarStageToLayer R D G x 0).f q) := by
  intro a b h
  apply Subtype.ext
  have hh := congrArg ((moduleDegreeEvaluation R D x q).map
    (dgCoherentBarLayerInclusion R D G 0)) h
  change (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G 0)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G 0) a.val) =
    (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G 0)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G 0) b.val) at hh
  rwa [dgCoherentBarZeroLayer_recover R D G x q a.val a.property,
    dgCoherentBarZeroLayer_recover R D G x q b.val b.property] at hh

def dgCoherentBarZeroStageIso (x : D) :
    dgCoherentBarNormalizedStageComplex R D G x 0 ≅
      (moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G 0) := by
  let f := dgCoherentBarStageToLayer R D G x 0
  letI : Mono f := HomologicalComplex.mono_of_mono_f f (fun q =>
    (ModuleCat.mono_iff_injective _).mpr (dgCoherentBarZeroStageToLayer_injective R D G x q))
  letI : Epi f := HomologicalComplex.epi_of_epi_f f (fun q =>
    (ModuleCat.epi_iff_surjective _).mpr (dgCoherentBarStageToLayer_surjective R D G x q 0))
  letI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

end SerrePositivity.InfinityCategories
