module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence

/-!
概要：面側が指定する共有境界像を保って、二次内ホーンの比較を厳密に可換にする。
方針：同じ指定自然性の path を分類先の Kan 制限で持ち上げる。
規約：元のホーン比較と元の分類主写像への大域同型を保持する。
使われ方：大域同型を伴う coherent な二次元境界比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison p q
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver 2 1)

local instance {D : SSet.{u}} (a : D ⟶ nerve (ULift.{u} (Fin 3))) :
    InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 面側から指定した自然性の同じ path を保つ厳密なホーン正方形。 -/
def cocartesianTwoHornCoherentHomCorrection :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare T H (N ≫ V) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceCoherenceIso j p q) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare T (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration T) H (N ≫ V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceCoherenceIso j p q)

/-- 面側の大域指定像と整合する、同じホーン比較の補正。 -/
def cocartesianTwoHornCoherentComparison := (cocartesianTwoHornCoherentHomCorrection j p q).map

/-- 同じ共有境界比較との厳密な可換式。 -/
lemma cocartesianTwoHornCoherentComparison_comm :
    cocartesianTwoHornCoherentComparison j p q ≫ T = N ≫ V :=
  (cocartesianTwoHornCoherentHomCorrection j p q).comm

/-- 元のホーン比較への同じ指定補正同型。 -/
def cocartesianTwoHornCoherentComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cocartesianTwoHornCoherentComparison j p q) H :=
  (cocartesianTwoHornCoherentHomCorrection j p q).exactComponentIso

/-- 面側と整合させた同じ補正ホーン比較自身も同値。 -/
lemma cocartesianTwoHornCoherentComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoHornCoherentComparison j p q) :=
  (cocartesianTwoHornCoherentHomCorrection j p q).map_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_isQCatEquivalence p q)

/-- 補正同型の共有境界像は、面側から指定した自然性そのもの。 -/
lemma cocartesianTwoHornCoherentComparisonIso_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((cocartesianTwoHornCoherentComparisonIso j p q).postcomp T)
      (cocartesianTwoHornCoherentComparison_comm j p q) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence.cocartesianTwoHornFaceCoherenceIso j p q :=
  (cocartesianTwoHornCoherentHomCorrection j p q).exactComponentIso_postcomp_normalized

/-- 同じ補正ホーン比較は、元の大域の分類作用と指定同型で結ばれる。 -/
def cocartesianTwoHornCoherentComparison_originalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ cocartesianTwoHornCoherentComparison j p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornOriginalTargetAction p q) :=
  (cocartesianTwoHornCoherentComparisonIso j p q).precomp R ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornCoherentCorrection
