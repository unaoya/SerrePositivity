module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRightZeroWitness
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareFrame
public import SerrePositivity.KST.SConstruction.StableZeroSquareComparison
public import SerrePositivity.KST.SConstruction.SquareFrameHomotopyPostcomp

/-!
概要：共通実 S 長方形の同じ右面を絶対恒等 lax 面へ全比較する。
方針：同じ四頂点成分付きの四辺比較を零対角で貼り、元 Cat^perf 全図式へ戻す。
規約：実右面の両二胞体を保持し、長方形全体の認証とは区別する。
使われ方：Sp-3 の右面認証と ActualRectangleInput.rightComparison。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "N" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ dgOdotMilnorActualRectangleDiagram R d
local notation "F" => (N) ≫ dgKInputPerfectNu R
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
local notation "G" => PerfectVerdierDiagram.square
  (PerfectVerdierSequence.presentation (perfectIdentityLaxSequence (Q) (hQ)))

/-- 概要：同じ実右面の四辺比較は元の四頂点経路を共有する。
方針：包含・商・二零辺の指定端点付き証人をそのまま一つの frame に束ねる。
規約：元全ホモトピーと元両面を保持。使われ方：零対角上の全四角形比較。 -/
def dgOdotMilnorActualRightSquareFrameComparison :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (F)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (G)) := by
  let wI := dgOdotMilnorActualRightInclusionWitness R d
  let wP := dgOdotMilnorActualRightProjectionWitness R d
  let wL := dgOdotMilnorActualRightZeroLeftWitness R d
  let wT := dgOdotMilnorActualRightZeroTopWitness R d
  let bH := specifiedSquareHomotopyWithEndpoints wI.homotopy
    (dgOdotMilnorActualRight_nu_inclusion R d).symm
    (PerfectVerdierSequence.presentation_bottom (perfectIdentityLaxSequence (Q) (hQ))).symm
  let rH : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (G)) :=
    specifiedSquareHomotopyWithEndpoints wP.homotopy
    (dgOdotMilnorActualRight_nu_projection R d).symm (by
      rw [PerfectVerdierSequence.presentation_right, perfectIdentityLaxSequence_projection]
      rfl)
  let lH := specifiedSquareHomotopyWithEndpoints wL.homotopy
    (dgOdotMilnorActualRight_nu_zero_inclusion R d).symm
    (dgOdotMilnorIdentityAbsoluteSquare_left R d).symm
  let tH := specifiedSquareHomotopyWithEndpoints wT.homotopy
    (dgOdotMilnorActualRight_nu_zero_extension R d).symm
    (dgOdotMilnorIdentityAbsoluteSquare_top R d).symm
  have hI := wI.isInvertible
    (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
      (dgOdotMilnorActualRightSourceEquivalence R d).isQCatEquivalence)
    (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
      (dgOdotMilnorRightAxisCompletedGluingEquivalence R d).isQCatEquivalence)
  have hP := wP.isInvertible
    (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
      (dgOdotMilnorRightAxisCompletedGluingEquivalence R d).isQCatEquivalence)
    (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
      (dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d).isQCatEquivalence)
  have hL := wL.isInvertible
    (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
      (dgOdotMilnorActualRightSourceEquivalence R d).isQCatEquivalence)
    (dgOdotMilnorActualRightNullZeroMap_isInvertible R d)
  have hT := wT.isInvertible (dgOdotMilnorActualRightNullZeroMap_isInvertible R d)
    (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
      (dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d).isQCatEquivalence)
  exact {
    bottom := bH
    right := rH
    left := lH
    top := tH
    lower_left := wI.source_path.trans wL.source_path.symm
    lower_right := wI.target_path.trans wP.source_path.symm
    upper_left := wT.source_path.trans wL.target_path.symm
    upper_right := wT.target_path.trans wP.target_path.symm
    bottom_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge bH
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy bH)
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy wI.homotopy) rfl).mpr hI)
    right_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge rH
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy rH)
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy wP.homotopy) rfl).mpr hP)
    left_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge lH
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy lH)
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy wL.homotopy) rfl).mpr hL)
    top_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge tH
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy tH)
        (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy wT.homotopy) rfl).mpr hT) }

/-- 概要：共通実右面の Cat^perf 全四角形は絶対恒等面と全関手同型を持つ。
方針：同じ四辺 frame を StableInfinity へ写し、零対角による全比較を充満包含で戻す。
規約：元両二胞体を保持。使われ方：右面 VerdierSquareDiagramIso の比較本体。 -/
def dgOdotMilnorActualRightPerfectSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F) (G) := by
  let H := squareFrameHomotopyPostcomp
    (dgOdotMilnorActualRightSquareFrameComparison R d) perfectStableInfinityInclusion
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((F) ≫
      perfectStableInfinityInclusion) 0 1)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F) 0 1))
    exact dgOdotMilnorActualRight_perfect_zero R d
  exact perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
    (stableZeroSquareComparison H hz)

/-- 概要：絶対恒等面から同じ実右面への全比較の三つの指定境界。
方針：構成済み全比較の元包含・元商・元零角制限を取り出す。
規約：同じ全比較と同じ実 S 面を保持。使われ方：Sp-3 右面認証の境界引数。 -/
def dgOdotMilnorActualRightBoundary (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (dgOdotMilnorActualRightDiagram R d h).square (F) where
  inclusion := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorActualRightPerfectSquareComparison R d).symm
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
  quotient := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorActualRightPerfectSquareComparison R d).symm
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
  zero := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorActualRightPerfectSquareComparison R d).symm
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner

/-- 概要：共通実長方形の右面の無条件の指定三境界付き全図式認証。
方針：実両二胞体を保つ全比較を同じ三制限とともに束ねる。
規約：Milnor 条件以外の入力なし。外周・全長方形認証とは区別する。
使われ方：ActualRectangleInput.rightComparison への供給。 -/
def dgOdotMilnorActualRightSquareDiagramIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (dgOdotMilnorActualRightDiagram R d h).square (F)
      (dgOdotMilnorActualRightBoundary R d h) where
  comparison := (dgOdotMilnorActualRightPerfectSquareComparison R d).symm
  inclusion_eq := rfl
  quotient_eq := rfl
  zero_eq := rfl

end SerrePositivity.KST.SConstruction
