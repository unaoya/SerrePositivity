module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerProjection
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerSurjectivity

/-!
概要：実 theta の直下層への射影と、貼り合わせた一次作用素の評価の一致。
方針：各 summand で高次項の射影零を使い、有限直和表示で全要素へ拡張する。
規約：元の coherent theta を保持し、内部 cycle に限定しない。
使われ方：実長完全列の連結射と一次ホモロジー作用素の同定。
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

set_option maxHeartbeats 800000 in
-- 同じ実列の全 Hom 制限と次数評価を照合する局所上限。
lemma dgCoherentBarLayerFirstHom_eval_ι (x : D) (q : ℤ) (n : ℕ)
    (s : dgCoherentBarLayerIndex I (n + 1))
    (a : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerFamily R D G (n + 1) s)) :
    (moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)
      (((moduleHomπ R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) x).f 1
          (dgCoherentBarNormalizedTheta R D G)).v q (q + 1) rfl
            ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1))
              ((moduleDegreeEvaluation R D x q).map
                (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1)) s) a))) =
    (((moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G (n + 1)))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)) x).f 1
        (dgCoherentBarLayerFirstHom R D G n)).v q (q + 1) rfl
          ((moduleDegreeEvaluation R D x q).map
            (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1)) s) a)) := by
  have hi := congrArg (fun f => (moduleDegreeEvaluation R D x q).map f a)
    (dgCoherentBarLayerInclusion_ι R D G (n + 1) s)
  have hi' : (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1))
      ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1)) s) a) =
    (moduleDegreeEvaluation R D x q).map
      (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s.val) a := by
    simpa only [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply] using! hi
  rw [hi', dgCoherentBarHomogeneous_pre_apply R D
    (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1)) s) 1,
      dgCoherentBarLayerFirstHom_restrict,
    dgCoherentBarHomogeneous_pre_apply R D
      (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s.val) 1,
      dgCoherentBarNormalizedTheta_restrict]
  rcases s with ⟨⟨⟨m, t⟩, ht⟩, h⟩
  change m = n + 1 at h
  subst m
  dsimp only [dgCoherentBarLayerFirstCoefficient]
  erw [dgCoherentBarHomogeneous_post_apply, dgCoherentBarHomogeneous_post_apply]
  rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact dgCoherentBarColumn_projected_first R D G t x q a

lemma dgCoherentBarLayerFirstHom_eval (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerGraded R D G (n + 1))) :
    (moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)
      (((moduleHomπ R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) x).f 1
          (dgCoherentBarNormalizedTheta R D G)).v q (q + 1) rfl
            ((moduleDegreeEvaluation R D x q).map
              (dgCoherentBarLayerInclusion R D G (n + 1)) z)) =
    (((moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G (n + 1)))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)) x).f 1
        (dgCoherentBarLayerFirstHom R D G n)).v q (q + 1) rfl z) := by
  obtain ⟨t, a, ha⟩ := moduleCofan_element_rep R
    (fun s => (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerFamily R D G (n + 1) s))
    _ (moduleCoproductDegreeIsColimit R D (dgCoherentBarLayerFamily R D G (n + 1)) x q) z
  rw [← ha]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact dgCoherentBarLayerFirstHom_eval_ι R D G x q n s (a s)

end SerrePositivity.InfinityCategories
