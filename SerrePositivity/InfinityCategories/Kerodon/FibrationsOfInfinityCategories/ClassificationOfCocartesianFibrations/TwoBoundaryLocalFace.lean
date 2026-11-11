module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryDiagramComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalOriginal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HornBoundaryDiagramPullbacks

/-!
概要：任意の二単体の欠けた面を、同じ共有境界上の比較と厳密に揃える。
方針：一次元の指定 path を保つ補正を、元の二単体の中間面に適用する。
規約：底への二単体写像の単射性を要求せず、元の全 Hom と指定同型を保持する。
使われ方：任意の底の二次元境界を面とホーンから貼り合わせる。

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
variable {C : Type u} [Category.{u} C] (j : Fin 2)
  (σ : (Δ[2] : SSet.{u}) ⟶ nerve C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ

/-- 元の二単体の中間面に対する、同じ境界固定補正。 -/
def cocartesianTwoBoundaryLocalFaceComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHom j τ p q

/-- 同じ面から共有境界への元の native 制限。 -/
def cocartesianTwoBoundaryLocalFaceNativeRestriction :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalSourceRestriction τ p q

/-- 同じ面から共有境界への元の分類先の制限。 -/
def cocartesianTwoBoundaryLocalFaceTargetRestriction :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalTargetRestriction τ p q

/-- 任意の二単体で、共有境界の同じ比較と厳密に可換。 -/
lemma cocartesianTwoBoundaryLocalFaceComparison_comm :
    cocartesianTwoBoundaryLocalFaceComparison j σ p q ≫
      cocartesianTwoBoundaryLocalFaceTargetRestriction σ p q =
    cocartesianTwoBoundaryLocalFaceNativeRestriction σ p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramComparison j τ p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHom_comm_diagram j τ p q

/-- 同じ補正比較は、任意の二単体で追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryLocalFaceComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoBoundaryLocalFaceComparison j σ p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHom_isQCatEquivalence j τ p q

instance cocartesianTwoBoundaryLocalFaceNativeRestriction_fibration :
    Fibration (cocartesianTwoBoundaryLocalFaceNativeRestriction σ p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalSourceRestriction_fibration τ p q

instance cocartesianTwoBoundaryLocalFaceTargetRestriction_fibration :
    Fibration (cocartesianTwoBoundaryLocalFaceTargetRestriction σ p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalTargetRestriction_fibration τ p q

/-- 同じ面の補正比較は、元の大域全 Hom の作用を指定同型で回収する。 -/
def cocartesianTwoBoundaryLocalFaceComparison_originalIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHom_originalIso j τ p q

/-- 補正同型の共有境界での像は、元の指定局所自然性そのもの。 -/
lemma cocartesianTwoBoundaryLocalFaceComparison_iso_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHomIso j τ p q).postcomp
        (cocartesianTwoBoundaryLocalFaceTargetRestriction σ p q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHom_comm j τ p q) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalNaturality.cocartesianOneBoundaryHomComparison_localNaturalityIso j τ p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryLocalCorrectedHomIso_boundary j τ p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
