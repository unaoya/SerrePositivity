module
public import SerrePositivity.InfinityCategories.Stable.TerminalComparisonFiberTransfer
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedSliceConeEquivalence

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
namespace SerrePositivity.InfinityCategories

/-- 内部 Hom の全錐の頂点射影の厳密 fiber は Kan 複体。 -/
instance coneFamilyApex_vertexFiber_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (vertexFiber (HomotopyLimits.coneFamilyApex p) x) :=
  inferInstanceAs (KanComplex (HomotopyLimits.fixedApexConeFamily p x))

/-- 極限錐への任意の比較の頂点射影は、同じ実区間写像空間との同値。 -/
lemma limitConeTerminalComparison_isQCatEquivalence {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (c : JoinCone p) (hc : IsLimitCone c) (x : X _⦋0⦌)
    (H : SSet.Homotopy (vertexFiberι (HomotopyLimits.coneFamilyApex p) x)
      (SSet.const ((sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c))) :
    IsQCatEquivalence (terminalComparisonIntervalFamily (HomotopyLimits.coneFamilyApex p)
      ((sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c) x
      (vertexFiberι (HomotopyLimits.coneFamilyApex p) x)
      (vertexFiberι_comp (HomotopyLimits.coneFamilyApex p) x) H) := by
  let F := sliceConeFamilyMap p
  let q := HomotopyLimits.coneFamilyApex p
  have hFt : IsTerminalVertex (F.app (Opposite.op ⦋0⦌) c) :=
    ((isQCatEquivalence_sliceConeFamilyMap p).choose.isTerminalVertex_iff c).mp hc
  exact terminalComparisonIntervalFamily_isQCatEquivalence_of_fiberEquivalence
    (sliceOverProjection p) F q (HomotopyLimits.sliceConeFamilyMap_apex p) c hc hFt x
    (HomotopyLimits.coneVertexFiberFamilyMap_isQCatEquivalence p x) H
end SerrePositivity.InfinityCategories
