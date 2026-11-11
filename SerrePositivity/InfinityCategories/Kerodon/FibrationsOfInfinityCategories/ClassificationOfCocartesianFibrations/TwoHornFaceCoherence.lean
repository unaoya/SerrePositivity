module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryFaceInducedOriginal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornSharedOriginal

/-!
概要：面側の大域同型が指定する共有境界像を、二次内ホーンの全 Hom へ反映する。
方針：同じ元の大域 Hom 上の三角形を、同値なホーン制限の前合成で反映する。
規約：元の分類主写像と面側から指定した共有境界像を保持する。
使われ方：大域同型を伴う coherent な二次元境界比較の貼合せ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver 2 1)
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison j τ p q
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison p q

local instance {D : SSet.{u}} (a : D ⟶ nerve (ULift.{u} (Fin 3))) :
    InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 面側が指定する共有境界の大域同型を、同じホーン経由の表示へ移す。 -/
def cocartesianTwoHornFaceInducedOriginalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ (N ≫ V)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedOriginalTargetAction p q) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryFaceInducedOriginalIso j τ p q
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramComparison] at h
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedNativeRestriction_original]
    rfl
  · rfl

/-- 同じ面側の指定像から反映した、ホーンの共有境界への逆向き自然性。 -/
def cocartesianTwoHornFaceCoherenceReverseIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (H ≫ T) (N ≫ V) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homTransportTriangleCoherence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedOriginalTargetAction p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornOriginalTargetAction p q) R T H (N ≫ V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q)
    (cocartesianTwoHornFaceInducedOriginalIso j p q)

/-- 面側と同じ共有境界像を指定した、全ホーン Hom 上の自然性。 -/
def cocartesianTwoHornFaceCoherenceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (N ≫ V) (H ≫ T) :=
  (cocartesianTwoHornFaceCoherenceReverseIso j p q).symm

/-- 同じ自然性の大域制限は、面側が指定した三角形そのものを回収する。 -/
lemma cocartesianTwoHornFaceCoherenceReverseIso_original :
    (cocartesianTwoHornFaceCoherenceReverseIso j p q).precomp R ≪≫
      cocartesianTwoHornFaceInducedOriginalIso j p q =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homTransportTriangleCoherence_identity
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedOriginalTargetAction p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornOriginalTargetAction p q) R T H (N ≫ V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornSharedTargetOriginalIso p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q)
    (cocartesianTwoHornFaceInducedOriginalIso j p q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornFaceCoherence
