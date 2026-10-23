module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoHornSharedRestrictions
public import SerrePositivity.InfinityCategories.F1.HomTransportTriangleIdentity

/-!
概要：二次内ホーンと共有境界の比較を、元の大域 Hom 上の同じ指定三角形で結ぶ。
方針：同じ二回の制限の厳密な一致と、既存の境界比較同型を使う。
規約：元の大域作用と指定同型の値を保持する。
使われ方：ホーン上の全 Hom へ指定自然性を降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 元の大域全 Hom 作用の、同じホーンへの制限。 -/
def cocartesianTwoHornOriginalTargetAction :=
  cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (cocartesianFiniteHornOver 2 1).hom) P Q

/-- 元の大域全 Hom 作用の、同じ共有境界への制限。 -/
def cocartesianTwoHornSharedOriginalTargetAction :=
  cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.shared 1 1 σ).hom) P Q

/-- 同じ target の二回の制限が与える、指定の恒等比較。 -/
def cocartesianTwoHornSharedTargetOriginalIso :
    FunctorIso (cocartesianTwoHornOriginalTargetAction p q ≫
      cocartesianTwoHornSharedTargetRestriction p q)
      (cocartesianTwoHornSharedOriginalTargetAction p q) := by
  have h : cocartesianTwoHornOriginalTargetAction p q ≫
      cocartesianTwoHornSharedTargetRestriction p q =
      cocartesianTwoHornSharedOriginalTargetAction p q := by
    rw [cocartesianTwoHornOriginalTargetAction, Category.assoc,
      cocartesianTwoHornSharedTargetRestriction_original]
    rfl
  exact eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f)) h)

/-- 同じ境界比較の元の指定同型を、ホーンを経由する制限の表示へ移す。 -/
def cocartesianTwoHornSharedNativeOriginalIso (j : Fin 2) :
    FunctorIso
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (cocartesianFiniteHornOver 2 1) ≫
        (cocartesianTwoHornSharedNativeRestriction p q ≫
          cocartesianOneBoundaryHomComparison j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q))
      (cocartesianTwoHornSharedOriginalTargetAction p q) := by
  apply F2.functorIsoOfEq
    (cocartesianOneBoundaryHomComparison_originalIso j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q)
  · rw [← Category.assoc, cocartesianTwoHornSharedNativeRestriction_original]
    rfl
  · rfl

end SerrePositivity.InfinityCategories
