module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryOriginal
public import SerrePositivity.InfinityCategories.F1.Cocartesian.NativeRestrictionFibration
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquarePrecompositionCoherence

/-!
概要：一次元境界の指定比較同型を保つ、元の全 Hom 作用の補正。
方針：分類先の境界制限の Kan 性で同じ指定 path を持ち上げる。
規約：元の作用への指定同型と境界比較そのものを保持する。
使われ方：区間の両端を固定した Hom の比較。
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
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) [Mono σ]
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (HornBoundaryOver.apex 0 σ)
/-- 同じ一次元境界への分類先の実際の制限。 -/
def cocartesianOneBoundaryTargetRestriction := intervalDiagramRestriction
  ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 σ).hom) P Q
local notation "T" => cocartesianOneBoundaryTargetRestriction σ p q
local notation "V" => cocartesianOneBoundaryHomComparison i σ p q
local notation "S" => cocartesianStraighteningHomInterval p q

/-- 同じ一次元境界の分類先制限は Kan fibration。 -/
lemma cocartesianOneBoundaryTargetRestriction_fibration : Fibration T := by
  have : Mono (HornBoundaryOver.apex 0 σ).hom :=
    inferInstanceAs (Mono ((boundary 1).ι ≫ σ))
  have := SimplicialModel.UniverseLift.mono_map (HornBoundaryOver.apex 0 σ).hom
  exact intervalDiagramRestriction_fibration _ P Q

/-- 元の指定同型の path を保ち、境界比較と厳密に可換にする。 -/
def cocartesianOneBoundaryHomCorrection :
    PathCorrectedFunctorSquare T S (R ≫ V)
      (cocartesianOneBoundaryHomComparison_originalIso i σ p q) := by
  haveI := cocartesianOneBoundaryTargetRestriction_fibration σ p q
  exact pathCorrectedFunctorSquare T (kanEquivalenceLifting_of_kanFibration T)
    S (R ≫ V) (cocartesianOneBoundaryHomComparison_originalIso i σ p q)

/-- 境界比較と厳密に可換な同じ全 Hom 作用。 -/
def cocartesianOneBoundaryCorrectedHom := (cocartesianOneBoundaryHomCorrection i σ p q).map

/-- 補正した作用の境界制限は、指定した元の境界比較そのもの。 -/
lemma cocartesianOneBoundaryCorrectedHom_comm :
    cocartesianOneBoundaryCorrectedHom i σ p q ≫ T = R ≫ V :=
  (cocartesianOneBoundaryHomCorrection i σ p q).comm

/-- 補正した作用は同じ指定 path で元の分類作用と同型。 -/
def cocartesianOneBoundaryCorrectedHomIso :
    FunctorIso (cocartesianOneBoundaryCorrectedHom i σ p q) S :=
  (cocartesianOneBoundaryHomCorrection i σ p q).exactComponentIso

/-- 補正同型の境界での像は、元の指定された境界比較同型そのもの。 -/
lemma cocartesianOneBoundaryCorrectedHomIso_boundary :
    F2.functorIsoOfEq ((cocartesianOneBoundaryCorrectedHomIso i σ p q).postcomp T)
      (cocartesianOneBoundaryCorrectedHom_comm i σ p q) rfl =
      cocartesianOneBoundaryHomComparison_originalIso i σ p q :=
  (cocartesianOneBoundaryHomCorrection i σ p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories
