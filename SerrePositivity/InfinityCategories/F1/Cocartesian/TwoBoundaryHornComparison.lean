module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryFaceComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RestrictionDiagramMaps

/-!
概要：二次内ホーンの補正比較を、同じ共有境界の反変図式の表示へ移す。
方針：元の制限と比較の端点表示のみを揃える。
規約：元の補正比較と指定 path を変更しない。
使われ方：同じ面側比較と厳密な cospan 比較を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 欠けた面の標準境界表示から、同じ元のホーンへの包含。 -/
def cocartesianTwoBoundarySharedToHorn :
    HornBoundaryOver.apex 0 (stdSimplex.δ (1 : Fin 3) ≫ (stdSimplex.isoNerve.{u} 2).hom) ⟶
      cocartesianFiniteHornOver.{u} 2 1 :=
  HornBoundaryOver.toHorn 1 1 (stdSimplex.isoNerve.{u} 2).hom

/-- 同じ標準境界表示の包含は、元の共有境界包含そのもの。 -/
lemma cocartesianTwoBoundarySharedToHorn_eq :
    cocartesianTwoBoundarySharedToHorn.{u} =
      HornBoundaryOver.toHorn 1 1 (stdSimplex.isoNerve.{u} 2).hom := rfl

/-- 同じホーンから共有境界への native 図式の射。 -/
def cocartesianTwoBoundaryHornNativeRestriction :=
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).map cocartesianTwoBoundarySharedToHorn.op

/-- 同じホーンから共有境界への分類先図式の射。 -/
def cocartesianTwoBoundaryHornTargetRestriction :=
  ((uliftOverFunctor (nerve (ULift.{u} (Fin 3)))).op ⋙
    intervalDiagramOverFunctor P Q).map cocartesianTwoBoundarySharedToHorn.op

/-- 反変 Hom 図式の両端に揃えた同じ補正ホーン比較。 -/
def cocartesianTwoBoundaryHornComparison :
    (((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
      SSet.uliftFunctor.{u + 1, u}).obj (Opposite.op (cocartesianFiniteHornOver 2 1))) ⟶
    (((uliftOverFunctor (nerve (ULift.{u} (Fin 3)))).op ⋙
      intervalDiagramOverFunctor P Q).obj (Opposite.op (cocartesianFiniteHornOver 2 1))) := by
  dsimp only [Functor.comp_obj, Functor.op_obj, uliftOverFunctor, intervalDiagramOverFunctor,
    cocartesianPullbackNativeCoreFunctor, cocartesianPullbackNativeFunctor]
  exact cocartesianTwoHornSharedCorrectedComparison j p q

/-- 同じ共有境界図式の表示で、補正ホーン比較は厳密に可換。 -/
lemma cocartesianTwoBoundaryHornComparison_comm :
    cocartesianTwoBoundaryHornComparison j p q ≫
      cocartesianTwoBoundaryHornTargetRestriction p q =
    cocartesianTwoBoundaryHornNativeRestriction p q ≫
      cocartesianOneBoundaryDiagramComparison j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q := by
  dsimp only [cocartesianTwoBoundaryHornComparison, cocartesianTwoBoundaryHornTargetRestriction,
    cocartesianTwoBoundaryHornNativeRestriction, cocartesianOneBoundaryDiagramComparison]
  rw [cocartesianTwoBoundarySharedToHorn_eq]
  have hc := cocartesianTwoHornSharedCorrectedComparison_comm j p q
  simp only [cocartesianTwoHornSharedNativeRestriction,
    cocartesianTwoHornSharedTargetRestriction, cocartesianPullbackNativeLiftPre_eq_diagramMap,
    intervalDiagramOverPre_ulift_eq_diagramMap] at hc
  dsimp only [id]
  dsimp only [Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
    uliftOverFunctor, intervalDiagramOverFunctor, cocartesianPullbackNativeCoreFunctor,
    cocartesianPullbackNativeFunctor, quasicategoryCoreFunctor, Quiver.Hom.unop_op] at hc ⊢
  exact hc

/-- 同じ反変図式の端点表示に揃えた補正ホーン比較も同値。 -/
lemma cocartesianTwoBoundaryHornComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoBoundaryHornComparison j p q) := by
  have hc := cocartesianTwoHornSharedCorrectedComparison_isQCatEquivalence j p q
  dsimp only [cocartesianTwoBoundaryHornComparison, id, Functor.comp_obj, Functor.op_obj,
    uliftOverFunctor, intervalDiagramOverFunctor, cocartesianPullbackNativeCoreFunctor,
    cocartesianPullbackNativeFunctor, quasicategoryCoreFunctor] at hc ⊢
  exact hc

end SerrePositivity.InfinityCategories
