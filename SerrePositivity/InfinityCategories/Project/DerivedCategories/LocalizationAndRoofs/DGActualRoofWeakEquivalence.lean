module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofFinitePairs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FiniteRelativeCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality

/-! # 実屋根の商比較の弱ホモトピー同値性

概要：平坦な Drinfeld 商への実屋根比較は left cofinal であり、弱ホモトピー同値である。
方針：全時刻整合的な有限対充填を一般判定へ渡し、全 Kan 標的の検査へ接続する。
規約：π₀ のみで弱同値性を定義しない。使われ方：dg 商の局所化の写像空間の比較。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 実屋根比較は一般の有限対の全時刻整合的相対充填条件を満たす。 -/
theorem dgRoofCorrespondenceMap_hasFiniteHomotopyRelativeFillers (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) := by
  intro L K i _ _ a g ha
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofFinitePairs_nonempty A D P hP x y i a g ha

/-- 平坦な商への実屋根比較は left cofinal。 -/
theorem dgRoofCorrespondenceMap_isLeftCofinal (P : Set D)
    (hP : localKFlat A D P) (x y : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers.isLeftCofinal
    (dgRoofCorrespondenceMap_hasFiniteHomotopyRelativeFillers A D P hP x y)

/-- 実屋根比較は、全 Kan 標的への前合成で検査する弱ホモトピー同値。 -/
theorem dgRoofCorrespondenceMap_isWeakHomotopyEquivalence (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) :=
  (dgRoofCorrespondenceMap_isLeftCofinal A D P hP x y).isWeakHomotopyEquivalence

/-- 実屋根比較に沿う前合成は任意の Kan 標的への写像空間のホモトピー同値。 -/
theorem dgRoofCorrespondenceMap_precompose_kan (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) (Z : SSet.{max u v}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)).app Z) :=
  (dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y).precompose_kan Z

/-- 連続 Kan 置換後の実屋根比較は quasicategory の同値となる。 -/
theorem dgRoofCorrespondenceMap_continuousKan_isQCatEquivalence (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y)
  exact h.isSimplicialHomotopyEquivalence.isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
