module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryHornComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSpanPullbackComparison

/-!
概要：二次境界のホーンと欠けた面の同じ厳密 cospan 比較は、pullback 上でも同値。
方針：共有境界・面・ホーンの三成分の同値と両側の面制限の Kan 性を使う。
規約：両補正の指定 path と元の pullback 比較写像を保持する。
使われ方：実際の二次元境界の Hom 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "p₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceNativeRestriction p q
local notation "p₂" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornNativeRestriction p q
local notation "q₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornTargetRestriction p q
local notation "v" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramComparison j
  (stdSimplex.δ (1 : Fin 3) ≫ Iso.hom (stdSimplex.isoNerve 2)) p q
local notation "f" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceComparison j p q
local notation "h" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornComparison j p q

local instance : HasPullback p₁ p₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan p₁ p₂)
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 同じ三成分の補正比較から作る、実際の二つの pullback の比較。 -/
def cocartesianTwoBoundaryPullbackComparison : pullback p₁ p₂ ⟶ pullback q₁ q₂ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap p₁ p₂ q₁ q₂ v f h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceComparison_comm j p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornComparison_comm j p q)

/-- 同じ pullback 比較の面側射影は、同じ補正面比較。 -/
lemma cocartesianTwoBoundaryPullbackComparison_fst :
    cocartesianTwoBoundaryPullbackComparison j p q ≫ pullback.fst q₁ q₂ =
      pullback.fst p₁ p₂ ≫ f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- 同じ pullback 比較のホーン側射影は、同じ補正ホーン比較。 -/
lemma cocartesianTwoBoundaryPullbackComparison_snd :
    cocartesianTwoBoundaryPullbackComparison j p q ≫ pullback.snd q₁ q₂ =
      pullback.snd p₁ p₂ ≫ h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 同じ二次元境界の pullback 比較自体は前合成同値。 -/
lemma cocartesianTwoBoundaryPullbackComparison_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (cocartesianTwoBoundaryPullbackComparison j p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanSpanPullbackMap_isPrecompositionEquivalence p₁ p₂ q₁ q₂ v f h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceComparison_comm j p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornComparison_comm j p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryDiagramComparison_isQCatEquivalence j
      (stdSimplex.δ (1 : Fin 3) ≫ (stdSimplex.isoNerve 2).hom) p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryFaceComparison_isQCatEquivalence j p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryHornComparison_isQCatEquivalence j p q)

instance cocartesianTwoBoundarySourcePullback_kan : KanComplex (pullback p₁ p₂) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanComplex_pullback_of_fibration p₁ p₂
instance cocartesianTwoBoundaryTargetPullback_kan : KanComplex (pullback q₁ q₂) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanComplex_pullback_of_fibration q₁ q₂

/-- 同じ実際の pullback 比較は、追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryPullbackComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoBoundaryPullbackComparison j p q) :=
  (cocartesianTwoBoundaryPullbackComparison_isPrecompositionEquivalence j p q).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
