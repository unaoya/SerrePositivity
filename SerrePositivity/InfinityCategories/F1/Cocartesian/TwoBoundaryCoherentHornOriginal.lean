module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryCoherentHorn

/-!
概要：図式の端点に揃えた coherent なホーン比較の大域同型と、同じ共有境界像。
方針：元の補正比較の大域同型とその指定像を、同じ端点表示へ移す。
規約：元の分類主写像と面側から指定した共有境界像を保持する。
使われ方：厳密 pullback 上で面・ホーンの大域同型を貼り合わせる。
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
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (cocartesianFiniteHornOver 2 1)

/-- 同じ図式表示の coherent なホーン比較を、元の大域作用へ戻す指定同型。 -/
def cocartesianTwoBoundaryCoherentHornComparison_originalIso :
    FunctorIso (R ≫ cocartesianTwoBoundaryCoherentHornComparison j p q)
      (cocartesianTwoHornOriginalTargetAction p q) := by
  have hc := cocartesianTwoHornCoherentComparison_originalIso j p q
  dsimp only [cocartesianTwoBoundaryCoherentHornComparison, id,
    cocartesianPullbackNativeLiftCoreFunctor, intervalDiagramLiftOverFunctor,
    Functor.comp_obj, Functor.op_obj, uliftOverFunctor, intervalDiagramOverFunctor,
    cocartesianPullbackNativeCoreFunctor, cocartesianPullbackNativeFunctor,
    quasicategoryCoreFunctor] at hc ⊢
  exact hc

/-- 同じ大域同型の共有境界像は、面側が指定した大域同型そのもの。 -/
lemma cocartesianTwoBoundaryCoherentHornComparison_originalIso_shared_heq :
    HEq ((cocartesianTwoBoundaryCoherentHornComparison_originalIso j p q).postcomp
      (cocartesianTwoBoundaryHornTargetRestriction p q))
      (cocartesianOneBoundaryFaceInducedOriginalIso j
        (stdSimplex.δ (1 : Fin 3) ≫ σ) p q) := by
  have hc := cocartesianTwoHornCoherentGlobalIso_shared_heq j p q
  dsimp only [cocartesianTwoBoundaryCoherentHornComparison_originalIso,
    cocartesianTwoBoundaryHornTargetRestriction]
  rw [cocartesianTwoBoundarySharedToHorn_eq]
  simp only [cocartesianTwoHornSharedTargetRestriction,
    intervalDiagramOverPre_ulift_eq_diagramMap] at hc
  dsimp only [id, cocartesianTwoBoundaryCoherentHornComparison,
    cocartesianPullbackNativeLiftCoreFunctor, intervalDiagramLiftOverFunctor,
    Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map, uliftOverFunctor,
    intervalDiagramOverFunctor, cocartesianPullbackNativeCoreFunctor,
    cocartesianPullbackNativeFunctor, quasicategoryCoreFunctor, Quiver.Hom.unop_op] at hc ⊢
  exact hc

end SerrePositivity.InfinityCategories
