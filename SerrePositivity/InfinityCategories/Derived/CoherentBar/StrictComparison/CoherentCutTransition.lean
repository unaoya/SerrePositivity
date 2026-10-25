module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutModule
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanInclusionComparison

/-!
概要：単体次元の上限を増やす元の実 dg 加群射を構成する。
方針：内部射の包含可換式から θ の可換式を導き、MC 微分変更後の射へ戻す。
規約：全次数成分は同じ部分族直和の包含である。
使われ方：実段階の列と全 bar への余錐。
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

def dgCoherentBarCutGradedMap {n m : ℕ} (_h : n ≤ m) :
    dgCoherentBarCutGraded R D G n ⟶ dgCoherentBarCutGraded R D G m :=
  dgCoherentBarCutInclusion R D G n ≫ dgCoherentBarCutProjection R D G m

@[reassoc]
lemma dgCoherentBarCutGradedMap_inclusion {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarCutGradedMap R D G h ≫ dgCoherentBarCutInclusion R D G m =
      dgCoherentBarCutInclusion R D G n := by
  apply Sigma.hom_ext
  intro s
  dsimp only [dgCoherentBarCutGradedMap]
  rw [Category.assoc, dgCoherentBarCutInclusion_ι_assoc,
    dgCoherentBarCutProjection_ι_assoc R D G m ⟨s.val, s.property.trans h⟩,
    dgCoherentBarCutInclusion_ι, dgCoherentBarCutInclusion_ι]

lemma dgCoherentBarCutGradedMap_theta {n m : ℕ} (h : n ≤ m) :
    (eHomWhiskerRight (Complex R) (dgCoherentBarCutGradedMap R D G h)
      (dgCoherentBarCutGraded R D G m)).f 1 (dgCoherentBarCutTheta R D G m) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarCutGraded R D G n)
      (dgCoherentBarCutGradedMap R D G h)).f 1 (dgCoherentBarCutTheta R D G n) :=
  dgBarModuleTheta_comparison_of_inclusions R D
    (dgCoherentBarCutInclusion R D G n) (dgCoherentBarCutInclusion R D G m)
    (dgCoherentBarCutProjection R D G m) (dgCoherentBarCutInclusion_projection R D G m)
    (dgCoherentBarCutGradedMap R D G h) (dgCoherentBarCutGradedMap_inclusion R D G h)
    _ _ _ (dgCoherentBarCutTheta_inclusion R D G n) (dgCoherentBarCutTheta_inclusion R D G m)

def dgCoherentBarCutModuleMap {n m : ℕ} (h : n ≤ m) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G n) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G m) :=
  dgBarMaurerCartanModuleMap R D _ _ (dgCoherentBarCutTheta_maurerCartan R D G n)
    (dgCoherentBarCutTheta_maurerCartan R D G m) (dgCoherentBarCutGradedMap R D G h)
    (dgCoherentBarCutGradedMap_theta R D G h)

@[simp]
lemma dgCoherentBarCutModuleMap_eval_f {n m : ℕ} (h : n ≤ m) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgCoherentBarCutModuleMap R D G h)).f q =
      ((moduleEvaluation R D x).map (dgCoherentBarCutGradedMap R D G h)).f q :=
  dgBarMaurerCartanModuleMap_eval_f R D _ _ _ _ _ _ x q

@[reassoc]
lemma dgCoherentBarCutModuleMap_inclusion {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarCutModuleMap R D G h ≫ dgCoherentBarCutModuleInclusion R D G m =
      dgCoherentBarCutModuleInclusion R D G n := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgCoherentBarCutModuleMap_eval_f, dgCoherentBarCutModuleInclusion_eval_f]
  rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
    dgCoherentBarCutGradedMap_inclusion]

end SerrePositivity.InfinityCategories
