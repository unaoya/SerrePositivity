module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologySum
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHomologyMap
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDegreeDifferential

/-!
概要：実一次ホモロジー作用素の各非退化列を同じ実面の交代和へ比較する。
方針：全 Hom の実制限と次数一ホモロジー射の前自然性を使う。
規約：元の層の実 summand 包含を保持する。
使われ方：層ホモロジー同型を通した非退化 bar 微分との比較。
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

lemma dgCoherentBarFirstLayerHomology_restrict (x : D) (q : ℤ) (n : ℕ)
    (s : I.nonDegenerate (n + 1)) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1))
        (dgCoherentBarLayerIndexEquiv I (n + 1) s))) q ≫
      dgCoherentBarFirstLayerHomologyMap R D G x q n =
    dgDegreeOneHomologyMap R (dgCoherentBarFirstColumnCochain R D G s.val x)
      (dgCoherentBarFirstColumnCochain_closed R D G s.val x) q := by
  apply dgDegreeOneHomologyMap_pre R
    ((moduleEvaluation R D x).map (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1))
      (dgCoherentBarLayerIndexEquiv I (n + 1) s)))
    (dgCoherentBarFirstLayerCochain R D G x n) (dgCoherentBarFirstLayerCochain_closed R D G x n)
    (dgCoherentBarFirstColumnCochain R D G s.val x)
    (dgCoherentBarFirstColumnCochain_closed R D G s.val x) q
  ext a
  have h := dgCoherentBarHomogeneous_pre_apply R D
    (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1)) (dgCoherentBarLayerIndexEquiv I (n + 1) s))
    1 (dgCoherentBarLayerFirstHom R D G n) x q a
  rw [dgCoherentBarLayerFirstHom_restrict] at h
  simpa only [dgCoherentBarFirstLayerCochain, dgCoherentBarFirstColumnCochain,
    ModuleCat.comp_apply] using! h.symm

lemma dgCoherentBarFirstLayerHomology_column_sum (x : D) (q : ℤ) (n : ℕ)
    (s : I.nonDegenerate (n + 1)) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarLayerFamily R D G (n + 1))
        (dgCoherentBarLayerIndexEquiv I (n + 1) s))) q ≫
      dgCoherentBarFirstLayerHomologyMap R D G x q n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      dgDegreeOneHomologyMap R (dgCoherentBarLayerFaceCochain R D G s.val i x)
        (dgCoherentBarLayerFaceCochain_closed R D G s.val i x) q :=
  (dgCoherentBarFirstLayerHomology_restrict R D G x q n s).trans
    (dgCoherentBarFirstColumnHomology_sum R D G s.val x q)

end SerrePositivity.InfinityCategories
