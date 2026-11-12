module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalRestrictions
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence

/-!
概要：任意の一単体の全局所 Hom 比較を、同じ境界比較と厳密に可換にする。
方針：分類先の単射境界制限で、元の指定自然性の path を持ち上げる。
規約：元の全局所比較への同型と、その境界での指定像を保持する。
使われ方：境界値を固定した任意の一単体の Hom 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalSourceRestriction σ p q
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalTargetRestriction σ p q
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison σ p q
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison i σ p q

/-- 同じ境界の指定自然性の path を保持した厳密な正方形。 -/
def cocartesianOneBoundaryLocalHomCorrection :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare T S (R ≫ V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalNaturality.cocartesianOneBoundaryHomComparison_localNaturalityIso i σ p q) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare T (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration T) S (R ≫ V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalNaturality.cocartesianOneBoundaryHomComparison_localNaturalityIso i σ p q)

/-- 同じ境界比較と厳密に可換な、元の全局所 Hom 比較の補正。 -/
def cocartesianOneBoundaryLocalCorrectedHom :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).map

/-- 補正した同じ作用は、指定境界比較と厳密に可換。 -/
lemma cocartesianOneBoundaryLocalCorrectedHom_comm :
    cocartesianOneBoundaryLocalCorrectedHom i σ p q ≫ T = R ≫ V :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).comm

/-- 同じ補正比較は元の全局所比較と指定同型で一致する。 -/
def cocartesianOneBoundaryLocalCorrectedHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cocartesianOneBoundaryLocalCorrectedHom i σ p q) S :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).exactComponentIso

/-- 同じ補正比較自体は、追加仮定なしに同値。 -/
lemma cocartesianOneBoundaryLocalCorrectedHom_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianOneBoundaryLocalCorrectedHom i σ p q) :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).map_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison_isQCatEquivalence σ p q)

/-- 補正同型の境界での像は、元の指定局所自然性そのもの。 -/
lemma cocartesianOneBoundaryLocalCorrectedHomIso_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((cocartesianOneBoundaryLocalCorrectedHomIso i σ p q).postcomp T)
      (cocartesianOneBoundaryLocalCorrectedHom_comm i σ p q) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalNaturality.cocartesianOneBoundaryHomComparison_localNaturalityIso i σ p q :=
  (cocartesianOneBoundaryLocalHomCorrection i σ p q).exactComponentIso_postcomp_normalized

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
