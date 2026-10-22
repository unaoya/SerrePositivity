module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornCoherentGlobalProjection
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryHornComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianHornBoundaryDiagramPullbacks

/-!
概要：面側の大域指定像と整合するホーン比較を、同じ境界 cospan の端点表示へ揃える。
方針：元の coherent な補正比較と制限の図式表示を計算する。
規約：同じ比較写像と指定 path を保持する。
使われ方：大域同型を貼れる coherent な境界 pullback 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "N" => cocartesianPullbackNativeLiftCoreFunctor p.val.hom q.val.hom
local notation "T" => intervalDiagramLiftOverFunctor
  (cocartesianStrictTransportCoherentDiagram p.val.hom)
  (cocartesianStrictTransportCoherentDiagram q.val.hom)

local instance (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex ((N).obj (Opposite.op z)) :=
  cocartesianNativeLiftCoreFunctor_obj_kan p.val.hom q.val.hom z
local instance (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex ((T).obj (Opposite.op z)) :=
  cocartesianIntervalLiftOverFunctor_obj_kan p q z

/-- 同じ反変図式の端点に揃えた、coherent な補正ホーン比較。 -/
def cocartesianTwoBoundaryCoherentHornComparison :
    (N).obj (Opposite.op (cocartesianFiniteHornOver 2 1)) ⟶
      (T).obj (Opposite.op (cocartesianFiniteHornOver 2 1)) := by
  dsimp only [cocartesianPullbackNativeLiftCoreFunctor, intervalDiagramLiftOverFunctor,
    Functor.comp_obj, Functor.op_obj, uliftOverFunctor, intervalDiagramOverFunctor,
    cocartesianPullbackNativeCoreFunctor, cocartesianPullbackNativeFunctor]
  exact cocartesianTwoHornCoherentComparison j p q

/-- 同じ共有境界比較との厳密な可換式。 -/
lemma cocartesianTwoBoundaryCoherentHornComparison_comm :
    cocartesianTwoBoundaryCoherentHornComparison j p q ≫
      cocartesianTwoBoundaryHornTargetRestriction p q =
    cocartesianTwoBoundaryHornNativeRestriction p q ≫
      cocartesianOneBoundaryDiagramComparison j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q := by
  dsimp only [cocartesianTwoBoundaryCoherentHornComparison,
    cocartesianTwoBoundaryHornTargetRestriction, cocartesianTwoBoundaryHornNativeRestriction,
    cocartesianOneBoundaryDiagramComparison]
  rw [cocartesianTwoBoundarySharedToHorn_eq]
  have hc := cocartesianTwoHornCoherentComparison_comm j p q
  simp only [cocartesianTwoHornSharedNativeRestriction,
    cocartesianTwoHornSharedTargetRestriction, cocartesianPullbackNativeLiftPre_eq_diagramMap,
    intervalDiagramOverPre_ulift_eq_diagramMap] at hc
  dsimp only [id, cocartesianPullbackNativeLiftCoreFunctor, intervalDiagramLiftOverFunctor,
    Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
    uliftOverFunctor, intervalDiagramOverFunctor, cocartesianPullbackNativeCoreFunctor,
    cocartesianPullbackNativeFunctor, quasicategoryCoreFunctor, Quiver.Hom.unop_op] at hc ⊢
  exact hc

/-- 同じ端点表示に揃えた coherent な補正比較自身も同値。 -/
lemma cocartesianTwoBoundaryCoherentHornComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoBoundaryCoherentHornComparison j p q) := by
  have hc := cocartesianTwoHornCoherentComparison_isQCatEquivalence j p q
  dsimp only [cocartesianTwoBoundaryCoherentHornComparison, id,
    cocartesianPullbackNativeLiftCoreFunctor, intervalDiagramLiftOverFunctor,
    Functor.comp_obj, Functor.op_obj, uliftOverFunctor, intervalDiagramOverFunctor,
    cocartesianPullbackNativeCoreFunctor, cocartesianPullbackNativeFunctor,
    quasicategoryCoreFunctor] at hc ⊢
  exact hc

end SerrePositivity.InfinityCategories
