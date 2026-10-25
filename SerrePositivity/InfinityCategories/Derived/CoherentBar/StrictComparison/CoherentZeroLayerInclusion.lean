module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutGradedSplitting
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutZero
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageIso

/-!
概要：零次元層の内部 dg 加群から実正規化 bar への閉じた包含。
方針：零段階への回収と θ の零段階での消滅を用いる。
規約：内部次数層の包含を実 dg 射として構成する。
使われ方：指定 native 増大の C1 ホモロジー増大との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgBarZeroLayerInclusion_mem (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G 0)).X q) :
    ((moduleEvaluation R D x).map (dgCoherentBarLayerInclusion R D G 0)).f q z ∈
      dgCoherentBarNormalizedDegreeFiltration R D G x q 0 := by
  have he := congrArg (fun f : dgCoherentBarLayerGraded R D G 0 ⟶
      dgCoherentBarNormalizedGraded R D G => ((moduleEvaluation R D x).map f).f q z)
    (dgCoherentBarLayerInclusion_cut_recover R D G 0)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] at he
  rw [← he]
  exact dgCoherentBarCutInclusion_mem R D G x q 0 _

lemma dgBarZeroLayerInclusion_theta :
    (eHomWhiskerRight (Complex R) (dgCoherentBarLayerInclusion R D G 0)
      (dgCoherentBarNormalizedGraded R D G)).f 1 (dgCoherentBarNormalizedTheta R D G) = 0 := by
  apply moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  erw [← dgCoherentBarHomogeneous_pre_apply R D (dgCoherentBarLayerInclusion R D G 0)
    1 (dgCoherentBarNormalizedTheta R D G) x q z]
  have h := dgCoherentBarNormalizedDegreeFiltration_zero_theta R D G x q _
    (dgBarZeroLayerInclusion_mem R D G x q z)
  simpa only [map_zero, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply] using! h

def dgBarZeroLayerInclusion : dgCoherentBarLayerGraded R D G 0 ⟶
    ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) :=
  (dgBarMaurerCartanZeroIso R D (dgCoherentBarLayerGraded R D G 0)).inv ≫
    dgBarMaurerCartanModuleMap R D 0 (dgCoherentBarNormalizedTheta R D G)
      (dgBarModuleZero_maurerCartan R D _) (dgCoherentBarNormalizedTheta_maurerCartan R D G
        (dgCoherentBarMaurerCartan_unconditional R D G))
      (dgCoherentBarLayerInclusion R D G 0)
      (by simpa only [map_zero] using! dgBarZeroLayerInclusion_theta R D G)

@[simp]
lemma dgBarZeroLayerInclusion_eval_f (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgBarZeroLayerInclusion R D G)).f q =
      ((moduleEvaluation R D x).map (dgCoherentBarLayerInclusion R D G 0)).f q := by
  simp only [dgBarZeroLayerInclusion, Functor.map_comp, HomologicalComplex.comp_f,
    dgBarMaurerCartanModuleMap_eval_f]
  have hi : ((moduleEvaluation R D x).map
      (dgBarMaurerCartanZeroIso R D (dgCoherentBarLayerGraded R D G 0)).inv).f q =
      𝟙 (((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G 0)).X q) := by
    rw [dgBarMaurerCartanZeroIso, moduleIsoMk_inv_eval]
    rfl
  rw [hi, Category.id_comp]

lemma dgBarZeroStage_inclusion (x : D) :
    (dgCoherentBarZeroStageIso R D G x).hom ≫
      (moduleEvaluation R D x).map (dgBarZeroLayerInclusion R D G) =
        dgCoherentBarNormalizedStageInclusion R D G x 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, dgBarZeroLayerInclusion_eval_f]
  exact dgCoherentBarZeroLayer_recover R D G x q z.val z.property

end SerrePositivity.InfinityCategories
