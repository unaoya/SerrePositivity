module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryFaceInducedOriginal
public import SerrePositivity.InfinityCategories.F1.Cocartesian.NativeGlobalDiagramRestriction

/-!
概要：面側の大域同型と共有境界像を、同じ反変 Hom 図式の端点に揃える。
方針：元の指定同型の端点だけを一般の一単体のまま正規化する。
規約：元の分類主写像と面側の指定共有境界像を保持する。
使われ方：具体的な境界 pullback の第一成分と共有境界像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (j : Fin 2)
  (τ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ図式の端点に揃えた、補正一単体比較と元の大域作用との指定同型。 -/
def cocartesianOneBoundaryDiagramOriginalIso :
    FunctorIso
      (cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom (Over.mk τ) ≫
        cocartesianOneBoundaryLocalCorrectedHom j τ p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramGlobalDiagramRestriction P Q (Over.mk τ)) := by
  have h := cocartesianOneBoundaryLocalCorrectedHom_originalIso j τ p q
  dsimp only [cocartesianNativeGlobalDiagramRestriction, intervalDiagramGlobalDiagramRestriction]
  exact h

/-- 同じ図式表示の大域同型の共有境界像は、元の面側の指定像。 -/
lemma cocartesianOneBoundaryDiagramOriginalIso_shared_heq :
    HEq ((cocartesianOneBoundaryDiagramOriginalIso j τ p q).postcomp
      (cocartesianOneBoundaryLocalTargetRestriction τ p q))
      (cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) := by
  have h := cocartesianOneBoundaryFaceInducedOriginalIso_heq j τ p q
  dsimp only [cocartesianOneBoundaryDiagramOriginalIso, cocartesianNativeGlobalDiagramRestriction,
    intervalDiagramGlobalDiagramRestriction, id, cocartesianPullbackNativeLiftCoreFunctor,
    intervalDiagramLiftOverFunctor, Functor.comp_obj, Functor.op_obj, uliftOverFunctor,
    intervalDiagramOverFunctor, cocartesianPullbackNativeCoreFunctor,
    cocartesianPullbackNativeFunctor, quasicategoryCoreFunctor] at h ⊢
  exact h

end SerrePositivity.InfinityCategories
