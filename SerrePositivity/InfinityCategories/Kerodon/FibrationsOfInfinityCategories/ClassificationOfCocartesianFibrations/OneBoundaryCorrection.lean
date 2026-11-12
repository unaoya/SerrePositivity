module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeRestrictionFibration
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence

/-!
概要：一次元境界の指定比較同型を保つ、元の全 Hom 作用の補正。
方針：分類先の境界制限の Kan 性で同じ指定 path を持ち上げる。
規約：元の作用への指定同型と境界比較そのものを保持する。
使われ方：区間の両端を固定した Hom の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) [Mono σ]
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ)
/-- 同じ一次元境界への分類先の実際の制限。 -/
def cocartesianOneBoundaryTargetRestriction := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction
  ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ).hom) P Q
local notation "T" => cocartesianOneBoundaryTargetRestriction σ p q
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison i σ p q
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q

/-- 同じ一次元境界の分類先制限は Kan fibration。 -/
lemma cocartesianOneBoundaryTargetRestriction_fibration : Fibration T := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ).hom :=
    inferInstanceAs (Mono ((boundary 1).ι ≫ σ))
  have := SimplicialModel.UniverseLift.mono_map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ).hom
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_fibration _ P Q

/-- 元の指定同型の path を保ち、境界比較と厳密に可換にする。 -/
def cocartesianOneBoundaryHomCorrection :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare T S (R ≫ V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginal.cocartesianOneBoundaryHomComparison_originalIso i σ p q) := by
  haveI := cocartesianOneBoundaryTargetRestriction_fibration σ p q
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare T (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration T)
    S (R ≫ V) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginal.cocartesianOneBoundaryHomComparison_originalIso i σ p q)

/-- 境界比較と厳密に可換な同じ全 Hom 作用。 -/
def cocartesianOneBoundaryCorrectedHom := (cocartesianOneBoundaryHomCorrection i σ p q).map

/-- 補正した作用の境界制限は、指定した元の境界比較そのもの。 -/
lemma cocartesianOneBoundaryCorrectedHom_comm :
    cocartesianOneBoundaryCorrectedHom i σ p q ≫ T = R ≫ V :=
  (cocartesianOneBoundaryHomCorrection i σ p q).comm

/-- 補正した作用は同じ指定 path で元の分類作用と同型。 -/
def cocartesianOneBoundaryCorrectedHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cocartesianOneBoundaryCorrectedHom i σ p q) S :=
  (cocartesianOneBoundaryHomCorrection i σ p q).exactComponentIso

/-- 補正同型の境界での像は、元の指定された境界比較同型そのもの。 -/
lemma cocartesianOneBoundaryCorrectedHomIso_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((cocartesianOneBoundaryCorrectedHomIso i σ p q).postcomp T)
      (cocartesianOneBoundaryCorrectedHom_comm i σ p q) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginal.cocartesianOneBoundaryHomComparison_originalIso i σ p q :=
  (cocartesianOneBoundaryHomCorrection i σ p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
