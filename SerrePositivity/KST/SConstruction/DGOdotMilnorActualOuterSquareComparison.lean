module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualOuterKernelWitness
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRightSquareComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorKernelOuterSquareDiagramIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：同じ共通実長方形の外周を元 LT 絶対外周へ全比較する。
方針：元厚核零化面へ四側面を共有端点付きで貼り、保存済み元外周認証と合成する。
規約：実外周の両二胞体・元二零角・既存指定三境界を保持する。
使われ方：Sp-3 の外周認証と ActualRectangleInput.outerComparison。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "O" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ dgOdotMilnorActualRectangleDiagram R d
local notation "F" => (O) ≫ dgKInputPerfectNu R
local notation "G" => dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R
local notation "KIn" => dgOdotMilnorFlatKernelInput R d
local notation "PIn" => dgOdotMilnorCellInput R d

/-- 概要：実外周と元厚核零化面の四側面は同じ元四頂点経路を共有する。
方針：元包含・商・二零辺の指定端点付き証人を一つの frame に束ねる。
規約：元両面と元全ホモトピーを保持。使われ方：零対角での全四角形比較。 -/
def dgOdotMilnorActualOuterKernelFrameComparison :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (F)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (G)) := by
  let wI := dgOdotMilnorActualOuterKernelInclusionWitness R d
  let wP := dgOdotMilnorActualOuterKernelProjectionWitness R d
  let wL := dgOdotMilnorActualOuterKernelZeroLeftWitness R d
  let wT := dgOdotMilnorActualOuterKernelZeroTopWitness R d
  have hF := dgOdotMilnorActualOuter_nu_edges R d
  have hG := dgOdotMilnorKernelNull_nu_edges R d
  let bH : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (G)) :=
    specifiedSquareHomotopyWithEndpoints wI.homotopy hF.1.symm hG.1.symm
  let rH : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (G)) :=
    specifiedSquareHomotopyWithEndpoints wP.homotopy hF.2.1.symm hG.2.1.symm
  let lH : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (G)) :=
    specifiedSquareHomotopyWithEndpoints wL.homotopy hF.2.2.1.symm hG.2.2.1.symm
  let tH : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (G)) :=
    specifiedSquareHomotopyWithEndpoints wT.homotopy hF.2.2.2.symm hG.2.2.2.symm
  have hKI := perfectStableHoArrow_isIso_of_isQCatEquivalence
    (𝟙 (dgKInputStableValue R (KIn)))
    (dgKInputStableValue_isIdempotentComplete R (KIn))
    (dgKInputStableValue_isIdempotentComplete R (KIn))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (dgKInputStableValue R (KIn)).obj).isQCatEquivalence
  have hPI := perfectStableHoArrow_isIso_of_isQCatEquivalence
    (𝟙 (dgKInputStableValue R (PIn)))
    (dgKInputStableValue_isIdempotentComplete R (PIn))
    (dgKInputStableValue_isIdempotentComplete R (PIn))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (dgKInputStableValue R (PIn)).obj).isQCatEquivalence
  have hTarget := perfectStableHoArrow_isIso_of_isQCatEquivalence
    (dgOdotMilnorActualRightTargetMap R d)
    (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorRightAxisIdentityDifferenceInput R d))
    (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))
    (dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d).isQCatEquivalence
  have hZero := dgOdotMilnorActualOuterKernelZeroMap_isInvertible R d
  have hI := wI.isInvertible hKI hPI
  have hP := wP.isInvertible hPI hTarget
  have hL := wL.isInvertible hKI hZero
  have hT := wT.isInvertible hZero hTarget
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

/-- 概要：同じ実外周の全四角形と元厚核零化面は全関手同型を持つ。
方針：元 frame を StableInfinity へ写して零対角で貼り、同じ充満包含で戻す。
規約：元両二胞体を保持。使われ方：元絶対外周認証への接続。 -/
def dgOdotMilnorActualOuterKernelPerfectComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F) (G) := by
  let H := squareFrameHomotopyPostcomp
    (dgOdotMilnorActualOuterKernelFrameComparison R d) perfectStableInfinityInclusion
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((F) ≫ perfectStableInfinityInclusion) 0 1)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F) 0 1))
    exact dgOdotMilnorActualOuter_perfect_zero R d
  exact perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
    (stableZeroSquareComparison H hz)

/-- 概要：元絶対外周の指定三境界を同じ元厚核全比較で実外周へ運ぶ。
方針：既存指定三比較に同じ新全比較の三制限を合成する。
規約：既存の元指定境界を保持。使われ方：実外周認証の境界引数。 -/
def dgOdotMilnorActualOuterBoundary (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (dgOdotMilnorActualOuterDiagram R d h).square (F) where
  inclusion := (dgOdotMilnorKernelOuterSquareBoundary R d h).inclusion ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorActualOuterKernelPerfectComparison R d).symm _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
  quotient := (dgOdotMilnorKernelOuterSquareBoundary R d h).quotient ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorActualOuterKernelPerfectComparison R d).symm _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
  zero := (dgOdotMilnorKernelOuterSquareBoundary R d h).zero ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorActualOuterKernelPerfectComparison R d).symm _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierZeroCorner

/-- 概要：共通実長方形の外周の指定三境界付き全図式認証。
方針：元厚核零化面への新全比較を保存済み絶対外周認証へ合成する。
規約：Milnor 条件以外の入力なし。元実外周を保持する。
使われ方：ActualRectangleInput.outerComparison への供給。 -/
def dgOdotMilnorActualOuterSquareDiagramIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (dgOdotMilnorActualOuterDiagram R d h).square (F)
      (dgOdotMilnorActualOuterBoundary R d h) where
  comparison := (dgOdotMilnorKernelOuterSquareDiagramIso R d h).comparison ≪≫
    (dgOdotMilnorActualOuterKernelPerfectComparison R d).symm
  inclusion_eq := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, (dgOdotMilnorKernelOuterSquareDiagramIso R d h).inclusion_eq]
    rfl
  quotient_eq := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, (dgOdotMilnorKernelOuterSquareDiagramIso R d h).quotient_eq]
    rfl
  zero_eq := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, (dgOdotMilnorKernelOuterSquareDiagramIso R d h).zero_eq]
    rfl

end SerrePositivity.KST.SConstruction
