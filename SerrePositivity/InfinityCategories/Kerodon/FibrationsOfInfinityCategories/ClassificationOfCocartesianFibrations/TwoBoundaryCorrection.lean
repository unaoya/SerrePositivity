module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryCoherentOriginal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryCorrection

/-!
概要：二次元境界の指定比較同型を保つ、元の全 Hom 作用の補正。
方針：同じ境界への分類先制限の Kan 性で、元の指定 path を持ち上げる。
規約：同じ実境界・全 Hom・元の分類主写像を保持する。
使われ方：指定境界値を固定した実際の fiber 比較。

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
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 1 σ
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom a
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramGlobalDiagramRestriction P Q a
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHomComparison j p q
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q

local instance twoBoundaryCorrectionTargetKan (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramLiftOverFunctor P Q).obj (Opposite.op z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalLiftOverFunctor_obj_kan p q z

/-- 同じ二次元実境界への分類先制限は Kan fibration。 -/
lemma cocartesianTwoBoundaryTargetRestriction_fibration : Fibration T := by
  have : Mono (a).hom :=
    inferInstanceAs (Mono ((boundary 2).ι ≫ (stdSimplex.isoNerve 2).hom))
  have := SimplicialModel.UniverseLift.mono_map (a).hom
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_fibration _ P Q

/-- 元の指定同型の path を保ち、実際の境界比較と厳密に可換にする。 -/
def cocartesianTwoBoundaryHomCorrection :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare T S (R ≫ V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHomComparison_originalIso j p q) := by
  haveI := cocartesianTwoBoundaryTargetRestriction_fibration p q
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare T (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration T)
    S (R ≫ V) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHomComparison_originalIso j p q)

/-- 同じ境界比較に厳密に可換な全 Hom 作用。 -/
def cocartesianTwoBoundaryCorrectedHom := (cocartesianTwoBoundaryHomCorrection j p q).map

/-- 補正した全作用の制限は、元の指定された境界比較そのもの。 -/
lemma cocartesianTwoBoundaryCorrectedHom_comm :
    cocartesianTwoBoundaryCorrectedHom j p q ≫ T = R ≫ V :=
  (cocartesianTwoBoundaryHomCorrection j p q).comm

/-- 同じ指定 path で、元の全分類作用を回収する。 -/
def cocartesianTwoBoundaryCorrectedHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cocartesianTwoBoundaryCorrectedHom j p q) S :=
  (cocartesianTwoBoundaryHomCorrection j p q).exactComponentIso

/-- 補正同型の境界像は、元の指定比較同型に厳密に一致する。 -/
lemma cocartesianTwoBoundaryCorrectedHomIso_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((cocartesianTwoBoundaryCorrectedHomIso j p q).postcomp T)
      (cocartesianTwoBoundaryCorrectedHom_comm j p q) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHomComparison_originalIso j p q :=
  (cocartesianTwoBoundaryHomCorrection j p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
