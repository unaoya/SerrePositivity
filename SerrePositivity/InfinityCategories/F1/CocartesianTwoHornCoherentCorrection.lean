module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornFaceCoherence
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquarePrecompositionCoherence

/-!
概要：面側が指定する共有境界像を保って、二次内ホーンの比較を厳密に可換にする。
方針：同じ指定自然性の path を分類先の Kan 制限で持ち上げる。
規約：元のホーン比較と元の分類主写像への大域同型を保持する。
使われ方：大域同型を伴う coherent な二次元境界比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "V" => cocartesianOneBoundaryHomComparison j (stdSimplex.δ (1 : Fin 3) ≫ σ) p q
local notation "N" => cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => cocartesianTwoHornNativeTargetComparison p q
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (cocartesianFiniteHornOver 2 1)

local instance {D : SSet.{u}} (a : D ⟶ nerve (ULift.{u} (Fin 3))) :
    InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 面側から指定した自然性の同じ path を保つ厳密なホーン正方形。 -/
def cocartesianTwoHornCoherentHomCorrection :
    PathCorrectedFunctorSquare T H (N ≫ V) (cocartesianTwoHornFaceCoherenceIso j p q) :=
  pathCorrectedFunctorSquare T (kanEquivalenceLifting_of_kanFibration T) H (N ≫ V)
    (cocartesianTwoHornFaceCoherenceIso j p q)

/-- 面側の大域指定像と整合する、同じホーン比較の補正。 -/
def cocartesianTwoHornCoherentComparison := (cocartesianTwoHornCoherentHomCorrection j p q).map

/-- 同じ共有境界比較との厳密な可換式。 -/
lemma cocartesianTwoHornCoherentComparison_comm :
    cocartesianTwoHornCoherentComparison j p q ≫ T = N ≫ V :=
  (cocartesianTwoHornCoherentHomCorrection j p q).comm

/-- 元のホーン比較への同じ指定補正同型。 -/
def cocartesianTwoHornCoherentComparisonIso :
    FunctorIso (cocartesianTwoHornCoherentComparison j p q) H :=
  (cocartesianTwoHornCoherentHomCorrection j p q).exactComponentIso

/-- 面側と整合させた同じ補正ホーン比較自身も同値。 -/
lemma cocartesianTwoHornCoherentComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoHornCoherentComparison j p q) :=
  (cocartesianTwoHornCoherentHomCorrection j p q).map_isQCatEquivalence
    (cocartesianTwoHornNativeTargetComparison_isQCatEquivalence p q)

/-- 補正同型の共有境界像は、面側から指定した自然性そのもの。 -/
lemma cocartesianTwoHornCoherentComparisonIso_boundary :
    F2.functorIsoOfEq ((cocartesianTwoHornCoherentComparisonIso j p q).postcomp T)
      (cocartesianTwoHornCoherentComparison_comm j p q) rfl =
      cocartesianTwoHornFaceCoherenceIso j p q :=
  (cocartesianTwoHornCoherentHomCorrection j p q).exactComponentIso_postcomp_normalized

/-- 同じ補正ホーン比較は、元の大域の分類作用と指定同型で結ばれる。 -/
def cocartesianTwoHornCoherentComparison_originalIso :
    FunctorIso (R ≫ cocartesianTwoHornCoherentComparison j p q)
      (cocartesianTwoHornOriginalTargetAction p q) :=
  (cocartesianTwoHornCoherentComparisonIso j p q).precomp R ≪≫
    cocartesianTwoHornNativeTargetComparison_originalIso p q

end SerrePositivity.InfinityCategories
