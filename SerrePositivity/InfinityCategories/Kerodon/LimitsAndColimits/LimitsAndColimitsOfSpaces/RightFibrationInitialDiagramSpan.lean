module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingDiagramRestriction

/-!
概要：始点を持つ図式の錐を使い、right fibration の二つの終点の比較を全族で結ぶ。
方針：始点の Hom への共通自明 Kan fibration の切断を選び、両端の元の切断と比較する。
規約：まずこの実錐からの終点への写像を保持し、標準の後合成との同定は別に行う。
使われ方：Kerodon §7.4、G8 の錐の辺の全族比較の共通 span。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

variable {K E B : SSet.{u}} [Quasicategory B] (r : E ⟶ B) [RightFibration r]
  (p : K ⟶ E) (a : (Δ[0] : SSet.{u}) ⟶ K) [Mono a]
  (ha : leftAnodyneExtensions a) (c : E _⦋0⦌)
  (hc : a ≫ p = SSet.yonedaEquiv.symm c) (x : B _⦋0⦌)

/-- 概要：同じ底の始点上の錐を、図式の始点への Hom に写す共通射影。
方針：図式を始点へ制限し、元の Hom 比較 span の射影を使う。
規約：元の図式 p を保持する。使われ方：錐の辺の両端の切断の比較。 -/
def rightFibrationInitialDiagramProjection :
    rightFibrationMappingDiagramTotal r p x ⟶ Basic.pinchedHom x (r.app _ c) :=
  rightFibrationMappingDiagramRestriction r p a hc x ≫
    rightFibrationMappingHomProjection r c x

include ha

/-- 共通射影は自明 Kan fibration。始点の包含と元の Hom 射影の二段で示す。 -/
lemma rightFibrationInitialDiagramProjection_trivialKanFibration :
    TrivialKanFibration (rightFibrationInitialDiagramProjection r p a c hc x) := by
  have : Quasicategory E := quasicategory_of_innerFibration r
  have ht := rightFibrationMappingDiagramRestriction_trivialKanFibration r p a ha hc x
  exact ⟨trivialKanFibrations.comp_mem _ _ ht.mem (TrivialKanFibration.mem
    (p := rightFibrationMappingHomProjection r c x))⟩

/-- 共通射影の実切断。各頂点で個別に持ち上げるのでなく Hom 空間全体を持ち上げる。 -/
def rightFibrationInitialDiagramSection :
    Basic.pinchedHom x (r.app _ c) ⟶ rightFibrationMappingDiagramTotal r p x := by
  letI := rightFibrationInitialDiagramProjection_trivialKanFibration r p a ha c hc x
  exact Classical.choose (trivialKanFibration_exists_section
    (rightFibrationInitialDiagramProjection r p a c hc x))

/-- 選んだ全族の切断は、共通射影に続けると厳密に恒等。 -/
lemma rightFibrationInitialDiagramSection_projection :
    rightFibrationInitialDiagramSection r p a ha c hc x ≫
        rightFibrationInitialDiagramProjection r p a c hc x = 𝟙 _ := by
  letI := rightFibrationInitialDiagramProjection_trivialKanFibration r p a ha c hc x
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (rightFibrationInitialDiagramProjection r p a c hc x))

/-- 概要：共通 span の始点側は、元の選択された Hom 比較に全族の同型で一致する。
方針：始点の自明 Kan fibration 上の二切断を比較し、同じ始点評価を後合成する。
規約：元の rightFibrationMappingSection を変えない。使われ方：辺の源の回収。 -/
def rightFibrationInitialDiagramSection_sourceIso :
    FunctorIso
      (rightFibrationInitialDiagramSection r p a ha c hc x ≫
        rightFibrationMappingDiagramEvaluation r p x)
      (rightFibrationHomComparison r c x) := by
  let H := functorIsoOfTrivialKanFibration (rightFibrationMappingHomProjection r c x)
    (rightFibrationInitialDiagramSection r p a ha c hc x ≫
      rightFibrationMappingDiagramRestriction r p a hc x)
    (rightFibrationMappingSection r c x) (by
      rw [Category.assoc, ← rightFibrationInitialDiagramProjection,
        rightFibrationInitialDiagramSection_projection, rightFibrationMappingSection_projection])
  have H' := H.postcomp (rightFibrationMappingEvaluation r c x)
  change FunctorIso
    ((rightFibrationInitialDiagramSection r p a ha c hc x ≫
      rightFibrationMappingDiagramRestriction r p a hc x) ≫
        rightFibrationMappingDiagramEvaluation r (SSet.yonedaEquiv.symm c) x)
    (rightFibrationHomComparison r c x) at H'
  simpa only [Category.assoc, rightFibrationMappingDiagramRestriction_evaluation] using H'

variable (b : (Δ[0] : SSet.{u}) ⟶ K) (d : E _⦋0⦌)
  (hd : b ≫ p = SSet.yonedaEquiv.symm d)

/-- 概要：共通 span の同じ切断を別の終点へ制限して得る、実際の Hom 空間間の射。
方針：図式 p の錐を残したまま、その終点への制限と元の射影を合成する。
規約：標準 PinchedInterval.postcompose との一致はここでは仮定しない。
使われ方：その一致を後で証明するための native な辺の全族。 -/
def rightFibrationInitialDiagramEndpointMap :
    Basic.pinchedHom x (r.app _ c) ⟶ Basic.pinchedHom x (r.app _ d) :=
  rightFibrationInitialDiagramSection r p a ha c hc x ≫
    rightFibrationMappingDiagramRestriction r p b hd x ≫
      rightFibrationMappingHomProjection r d x

/-- 概要：二終点の表現可能比較は、共通 span から得る実際の射に関して全族で可換。
方針：終点側の共通自明 Kan fibration 上の二持ち上げを比較し、源の回収と合成する。
規約：全パラメータを保つ。標準後合成との同定を結論に含めたとは扱わない。
使われ方：錐の辺に沿う G8 比較の前段。 -/
def rightFibrationInitialDiagramEndpointIso :
    FunctorIso (rightFibrationHomComparison r c x)
      (rightFibrationInitialDiagramEndpointMap r p a ha c hc x b d hd ≫
        rightFibrationHomComparison r d x) := by
  let H := functorIsoOfTrivialKanFibration (rightFibrationMappingHomProjection r d x)
    (rightFibrationInitialDiagramSection r p a ha c hc x ≫
      rightFibrationMappingDiagramRestriction r p b hd x)
    (rightFibrationInitialDiagramEndpointMap r p a ha c hc x b d hd ≫
      rightFibrationMappingSection r d x) (by
      simp only [Category.assoc, rightFibrationMappingSection_projection, Category.comp_id]
      rfl)
  have H' : FunctorIso
      (rightFibrationInitialDiagramSection r p a ha c hc x ≫
        rightFibrationMappingDiagramEvaluation r p x)
      (rightFibrationInitialDiagramEndpointMap r p a ha c hc x b d hd ≫
        rightFibrationHomComparison r d x) := by
    have H1 := H.postcomp (rightFibrationMappingEvaluation r d x)
    change FunctorIso
      ((rightFibrationInitialDiagramSection r p a ha c hc x ≫
        rightFibrationMappingDiagramRestriction r p b hd x) ≫
          rightFibrationMappingDiagramEvaluation r (SSet.yonedaEquiv.symm d) x)
      (rightFibrationInitialDiagramEndpointMap r p a ha c hc x b d hd ≫
        rightFibrationHomComparison r d x) at H1
    simpa only [Category.assoc, rightFibrationMappingDiagramRestriction_evaluation] using H1
  exact (rightFibrationInitialDiagramSection_sourceIso r p a ha c hc x).symm ≪≫ H'

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
