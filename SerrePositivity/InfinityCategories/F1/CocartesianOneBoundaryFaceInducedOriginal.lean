module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryLocalOriginal
public import SerrePositivity.InfinityCategories.F1.CocartesianRestrictionDiagramMaps

/-!
概要：面側の補正比較の大域同型から、同じ共有境界比較の大域同型を指定する。
方針：同じ target 境界制限で後合成し、両端を直接制限へ揃える。
規約：元の分類主写像・同じ境界比較と面側の指定同型を保持する。
使われ方：ホーン側の共有境界像を面側と構成時に揃える。
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
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (Over.mk τ)
local notation "U" => cocartesianOneBoundaryLocalCorrectedHom j τ p q
local notation "T" => cocartesianOneBoundaryLocalTargetRestriction τ p q
local notation "V" => cocartesianOneBoundaryDiagramComparison j τ p q

/-- 面側の補正作用を境界へ制限した始点は、元の直接境界制限と同じ比較。 -/
lemma cocartesianOneBoundaryFaceInducedOriginal_source :
    (R ≫ U) ≫ T =
      cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.apex 0 τ) ≫ V := by
  rw [Category.assoc, cocartesianOneBoundaryLocalCorrectedHom_comm_diagram,
    cocartesianOneBoundaryLocalSourceRestriction,
    ← cocartesianPullbackNativeLiftPre_eq_diagramMap, ← Category.assoc,
    cocartesianPullbackNativeLiftRestriction_naturality]

/-- 元の大域作用も、二回の同じ制限は直接境界制限と一致する。 -/
lemma cocartesianOneBoundaryFaceInducedOriginal_target :
    (cocartesianStraighteningHomInterval p q ≫
      intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map τ) P Q) ≫ T =
    cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 τ).hom) P Q := by
  rw [Category.assoc, cocartesianOneBoundaryLocalTargetRestriction,
    ← intervalDiagramOverPre_ulift_eq_diagramMap]
  exact congrArg (fun k ↦ cocartesianStraighteningHomInterval p q ≫ k)
    (intervalDiagramOverPre_restriction P Q (uliftOverMorphism (boundarySimplexOverMap 0 τ)))

/-- 同じ面側の大域同型を制限して指定する、共有境界比較の大域同型。 -/
def cocartesianOneBoundaryFaceInducedOriginalIso :
    FunctorIso
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.apex 0 τ) ≫ V)
      (cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 τ).hom) P Q) :=
  F2.functorIsoOfEq ((cocartesianOneBoundaryLocalCorrectedHom_originalIso j τ p q).postcomp T)
    (cocartesianOneBoundaryFaceInducedOriginal_source j τ p q)
    (cocartesianOneBoundaryFaceInducedOriginal_target τ p q)

/-- 同じ共有境界の指定同型は、面側の大域同型の指定像そのもの。 -/
lemma cocartesianOneBoundaryFaceInducedOriginalIso_heq :
    HEq ((cocartesianOneBoundaryLocalCorrectedHom_originalIso j τ p q).postcomp T)
      (cocartesianOneBoundaryFaceInducedOriginalIso j τ p q) :=
  (F2.functorIsoOfEq_heq _ _ _).symm

end SerrePositivity.InfinityCategories
