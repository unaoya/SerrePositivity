module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationModuleNerveIso
/-!
概要：同じ代表 Hom の native 空間関手を、実評価加群の基礎空間関手へ比較する。
方針：全 R 加群値 nerve 比較を同じ対象持ち上げと基礎空間関手で後合成する。
規約：κ と添字宇宙は u のまま、元の全 coherent 図式に適用できる。
使われ方：coherent C1 の評価余錐比較を c2 へ渡す最終の関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ射影的加群を x で評価し、その実 R 加群の全基礎空間を取る関手。 -/
def dgBarCompactProjectiveEvaluationSpaceInfinity (x : D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (dgProjectiveModuleNerve R D) ⟶ SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerve.map ((dgBarCompactProjectiveEvaluationModuleDG R D x).comp
        (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})))) ≫
    dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D)

/-- 同じ代表の全 native Hom と、同じ実評価の基礎空間の全関手同型。 -/
def dgBarCompactProjectiveEvaluationSpaceIso (x : D) :
    FunctorIso
      (dgHomTargetUnderlyingSpaceInfinity R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x))
      (dgBarCompactProjectiveEvaluationSpaceInfinity R D x) := by
  let Q := dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})
  have e := (dgBarCompactProjectiveEvaluationModuleNerveIso.{u, v, max (u + 1) v + 1}
    R D x).postcomp
      (dgNerveCommonMap.{u, u + 1, max (u + 1) v, max (u + 1) v + 1} Q)
  have h₁ := dgNerveCommonMap_comp.{u, max (u + 1) v, u + 1,
    max (u + 1) v, max (u + 1) v + 1} (R := R)
      (dgHomTargetModuleDG R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x)) Q
  have h₂ := dgNerveCommonMap_comp.{u, max (u + 1) v, u + 1,
    max (u + 1) v, max (u + 1) v + 1} (R := R)
      (dgBarCompactProjectiveEvaluationModuleDG R D x) Q
  change dgNerveCommonMap.{u, max (u + 1) v, u + 1, max (u + 1) v + 1}
      (dgHomTargetModuleDG R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x)) ≫
      dgNerveCommonMap.{u, u + 1, max (u + 1) v, max (u + 1) v + 1} Q =
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerve.map (dgHomTargetModuleLift R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x))) at h₁
  change dgNerveCommonMap.{u, max (u + 1) v, u + 1, max (u + 1) v + 1}
      (dgBarCompactProjectiveEvaluationModuleDG R D x) ≫
      dgNerveCommonMap.{u, u + 1, max (u + 1) v, max (u + 1) v + 1} Q =
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerve.map ((dgBarCompactProjectiveEvaluationModuleDG R D x).comp Q)) at h₂
  rw [h₁, h₂] at e
  exact e.postcomp (dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D))

/-- 同じ代表の native compact 性は、実評価空間の全 native 余極限保存と同値。 -/
lemma dgBarCompactRepresentable_iff_evaluation_preserves (κ : Cardinal.{u}) (x : D) :
    dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) (representable R x)) ↔
      F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
        (dgBarCompactProjectiveEvaluationSpaceInfinity R D x) := by
  apply (dgBarCompactRepresentable_iff_hom_preserves R D κ x).trans
  constructor
  · intro h
    exact h.of_functorIso (dgBarCompactProjectiveEvaluationSpaceIso R D x)
  · intro h
    exact h.of_functorIso (dgBarCompactProjectiveEvaluationSpaceIso R D x).symm

end SerrePositivity.InfinityCategories
