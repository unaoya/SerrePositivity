module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalComparisonFiberTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedSliceConeEquivalence

/-!
概要：極限錐への任意の比較が誘導する同じ実区間族の同値性。
方針：全パラメータの実比較を保持し、終対象性と厳密な fiber の比較を使う。
規約：安定性や有限極限を先取りしない。使われ方：一般安定性判定の実錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 内部 Hom の全錐の頂点射影の厳密 fiber は Kan 複体。 -/
instance coneFamilyApex_vertexFiber_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x))

/-- 極限錐への任意の比較の頂点射影は、同じ実区間写像空間との同値。 -/
lemma limitConeTerminalComparison_isQCatEquivalence {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (x : X _⦋0⦌)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c) x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x) H) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p
  have hFt : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F.app (Opposite.op ⦋0⦌) c) :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap p).choose.isTerminalVertex_iff c).mp hc
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_isQCatEquivalence_of_fiberEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) F q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_apex p) c hc hFt x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberFamilyMap_isQCatEquivalence p x) H
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
