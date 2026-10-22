module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornSharedNaturality
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquarePrecompositionCoherence

/-!
概要：二次内ホーンの比較を、同じ共有境界比較と指定 path を保って厳密に可換にする。
方針：分類先の共有境界制限の Kan 性で指定自然性を持ち上げる。
規約：元のホーン比較とその大域三角形を保持する。
使われ方：欠けた面の補正比較と実際の境界へ貼り合わせる。
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

local instance {D : SSet.{u}} (a : D ⟶ nerve (ULift.{u} (Fin 3))) :
    InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 元の共有境界の指定自然性の path を保つ、厳密な比較正方形。 -/
def cocartesianTwoHornSharedHomCorrection :
    PathCorrectedFunctorSquare T H (N ≫ V)
      (cocartesianTwoHornSharedComparisonNaturalityIso j p q) :=
  pathCorrectedFunctorSquare T (kanEquivalenceLifting_of_kanFibration T) H (N ≫ V)
    (cocartesianTwoHornSharedComparisonNaturalityIso j p q)

/-- 同じ共有境界比較と厳密に可換にしたホーン比較。 -/
def cocartesianTwoHornSharedCorrectedComparison := (cocartesianTwoHornSharedHomCorrection j p q).map

/-- 補正した比較の共有境界像は、同じ指定境界比較。 -/
lemma cocartesianTwoHornSharedCorrectedComparison_comm :
    cocartesianTwoHornSharedCorrectedComparison j p q ≫ T = N ≫ V :=
  (cocartesianTwoHornSharedHomCorrection j p q).comm

/-- 元のホーン比較への同じ指定同型。 -/
def cocartesianTwoHornSharedCorrectedComparisonIso :
    FunctorIso (cocartesianTwoHornSharedCorrectedComparison j p q) H :=
  (cocartesianTwoHornSharedHomCorrection j p q).exactComponentIso

/-- 同じ補正ホーン比較自体は、追加仮定なしに同値。 -/
lemma cocartesianTwoHornSharedCorrectedComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoHornSharedCorrectedComparison j p q) :=
  (cocartesianTwoHornSharedHomCorrection j p q).map_isQCatEquivalence
    (cocartesianTwoHornNativeTargetComparison_isQCatEquivalence p q)

/-- 補正同型の共有境界像は元の指定自然性そのもの。 -/
lemma cocartesianTwoHornSharedCorrectedComparisonIso_boundary :
    F2.functorIsoOfEq ((cocartesianTwoHornSharedCorrectedComparisonIso j p q).postcomp T)
      (cocartesianTwoHornSharedCorrectedComparison_comm j p q) rfl =
      cocartesianTwoHornSharedComparisonNaturalityIso j p q :=
  (cocartesianTwoHornSharedHomCorrection j p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories
