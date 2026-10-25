module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StableProjectionCompatibility
public import SerrePositivity.DifferentialGraded.Module.GradedCoproduct
/-!
概要：正規化 bar への実閉射影は、元の次数付き射影と同じ成分を持つ。
方針：MC 射の閉零サイクルを評価し、元の次数付き包含による切断を保つ。
規約：切断には鎖条件を課さない。閉包含は安定自己写像によって別に補正する。
使われ方：修正包含の閉性と射影との分裂式を、同じ全次数 dg 作用のもとで検証する。
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
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNormalizedModuleProjection_evaluation_f (x : D) (n : ℤ) :
    ((moduleEvaluation R D x).map
      (dgCoherentBarNormalizedModuleProjection R D F hMC)).f n =
    ((moduleEvaluation R D x).map (dgCoherentBarNormalizedProjection R D F)).f n := by
  have h := moduleEvaluation_cochain R D x
    (dgCoherentBarNormalizedModuleProjection R D F hMC)
  rw [dgCoherentBarNormalizedModuleProjection, dgCoherentBarMaurerCartanMap,
    moduleMorphismOfCycle_cycle] at h
  unfold dgCoherentBarMaurerCartanMapElement at h
  rw [moduleHomElementMk_π] at h
  have hv := congrArg (fun c => c.v n n (add_zero n)) h
  have ho := moduleEvaluation_cochain R D x (dgCoherentBarNormalizedProjection R D F)
  have hov := congrArg (fun c => c.v n n (add_zero n)) ho
  exact hv.trans hov.symm

abbrev dgCoherentBarNormalizedGradedSection (x : D) (n : ℤ) :
    ((moduleEvaluation R D x).obj
      (ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC))).X n ⟶
    ((moduleEvaluation R D x).obj (dgCoherentBarObject R D F hMC)).X n :=
  ((moduleEvaluation R D x).map (dgCoherentBarNormalizedInclusion R D F)).f n

lemma dgCoherentBarNormalizedGradedSection_projection (x : D) (n : ℤ) :
    dgCoherentBarNormalizedGradedSection R D F hMC x n ≫
      ((moduleEvaluation R D x).map
        (dgCoherentBarNormalizedModuleProjection R D F hMC)).f n = 𝟙 _ := by
  rw [dgCoherentBarNormalizedModuleProjection_evaluation_f]
  change ((moduleEvaluation R D x).map (dgCoherentBarNormalizedInclusion R D F)).f n ≫ _ = _
  rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
    dgCoherentBarNormalizedInclusion_projection, CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
  rfl

lemma dgCoherentBarNormalizedGradedSection_naturality
    (x y : D) (q i j : ℤ) (hij : i + q = j)
    (f : GradedHom R (Opposite.op x) (Opposite.op y) q) :
    moduleActionComponent R D
        (ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC))
        x y q i j hij f ≫ dgCoherentBarNormalizedGradedSection R D F hMC y j =
      dgCoherentBarNormalizedGradedSection R D F hMC x i ≫
        moduleActionComponent R D (dgCoherentBarObject R D F hMC) x y q i j hij f := by
  exact moduleMorphism_actionComponent R D (dgCoherentBarNormalizedInclusion R D F)
    x y q i j hij f

end SerrePositivity.InfinityCategories
