module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterSquareWitnesses
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareFrame

/-!
概要：元実外周の指定四側面を同じ四頂点経路で束ねる。
方針：元包含・商・零二側面の証人の全経路を回収する。
規約：元始域の増大屋根と実 resolved 商を保持。D2 入力は仮定しない。
使われ方：元 LT 外周への全四角形比較と指定三境界の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元実外周下辺を元指定全ホモトピーで比較する。
方針：元証人の端点表示を同じ四辺へ照合する。規約：全写像を保持。
使われ方：元外周全比較の指定下側面。 -/
def dgOdotMilnorOuterBottomHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  specifiedSquareHomotopyWithEndpoints (dgOdotMilnorOuterInclusionWitness R d).homotopy
    (dgOdotMilnorSourceNullOuterSquare_perfect_inclusion R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_inclusion R d h).symm

/-- 概要：元実外周右辺を元指定全ホモトピーで比較する。
方針：元証人の端点表示を同じ四辺へ照合する。規約：全写像を保持。
使われ方：元外周全比較の指定右側面。 -/
def dgOdotMilnorOuterRightHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  specifiedSquareHomotopyWithEndpoints (dgOdotMilnorOuterProjectionWitness R d h).homotopy
    (dgOdotMilnorSourceNullOuterSquare_perfect_projection R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_projection R d h).symm

/-- 概要：元実外周左辺を元指定全ホモトピーで比較する。
方針：元証人の端点表示を同じ四辺へ照合する。規約：全写像を保持。
使われ方：元外周全比較の指定左側面。 -/
def dgOdotMilnorOuterLeftHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  specifiedSquareHomotopyWithEndpoints (dgOdotMilnorOuterZeroLeftWitness R d).homotopy
    (dgOdotMilnorSourceNullOuterSquare_perfect_left R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_left R d h).symm

/-- 概要：元実外周上辺を元指定全ホモトピーで比較する。
方針：元証人の端点表示を同じ四辺へ照合する。規約：全写像を保持。
使われ方：元外周全比較の指定上側面。 -/
def dgOdotMilnorOuterTopHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  specifiedSquareHomotopyWithEndpoints (dgOdotMilnorOuterZeroTopWitness R d).homotopy
    (dgOdotMilnorSourceNullOuterSquare_perfect_top R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_top R d h).symm

/-- 概要：元実外周下側面の全比較は可逆。
方針：元指定二頂点経路の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：元外周全比較の可逆性。 -/
lemma dgOdotMilnorOuterBottomHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterBottomHomotopy R d h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterBottomHomotopy R d h))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterInclusionWitness R d).homotopy) rfl).mpr
    ((dgOdotMilnorOuterInclusionWitness R d).isInvertible (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence) (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence))

/-- 概要：元実外周右側面の全比較は可逆。
方針：元指定二頂点経路の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：元外周全比較の可逆性。 -/
lemma dgOdotMilnorOuterRightHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterRightHomotopy R d h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterRightHomotopy R d h))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterProjectionWitness R d h).homotopy) rfl).mpr
    ((dgOdotMilnorOuterProjectionWitness R d h).isInvertible (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence) (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (Q).obj).isQCatEquivalence))

/-- 概要：元実外周左側面の全比較は可逆。
方針：元指定二頂点経路の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：元外周全比較の可逆性。 -/
lemma dgOdotMilnorOuterLeftHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterLeftHomotopy R d h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterLeftHomotopy R d h))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterZeroLeftWitness R d).homotopy) rfl).mpr
    ((dgOdotMilnorOuterZeroLeftWitness R d).isInvertible (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence) (dgOdotMilnorOuterNullZeroMap_isInvertible R d))

/-- 概要：元実外周上側面の全比較は可逆。
方針：元指定二頂点経路の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：元外周全比較の可逆性。 -/
lemma dgOdotMilnorOuterTopHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterTopHomotopy R d h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterTopHomotopy R d h))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterZeroTopWitness R d).homotopy) rfl).mpr
    ((dgOdotMilnorOuterZeroTopWitness R d).isInvertible (dgOdotMilnorOuterNullZeroMap_isInvertible R d) (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (Q).obj).isQCatEquivalence))

/-- 概要：元実外周 LowerLeft の二側面は同じ頂点経路を共有する。
方針：元証人の同じ端点式を使う。規約：元全経路を保持。
使われ方：元四境界比較の接合。 -/
lemma dgOdotMilnorOuterLowerLeftHomotopy_path :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterBottomHomotopy R d h).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterLeftHomotopy R d h).h :=
  (dgOdotMilnorOuterInclusionWitness R d).source_path.trans
    (dgOdotMilnorOuterZeroLeftWitness R d).source_path.symm

/-- 概要：元実外周 LowerRight の二側面は同じ頂点経路を共有する。
方針：元証人の同じ端点式を使う。規約：元全経路を保持。
使われ方：元四境界比較の接合。 -/
lemma dgOdotMilnorOuterLowerRightHomotopy_path :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterBottomHomotopy R d h).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterRightHomotopy R d h).h :=
  (dgOdotMilnorOuterInclusionWitness R d).target_path.trans
    (dgOdotMilnorOuterProjectionWitness R d h).source_path.symm

/-- 概要：元実外周 UpperLeft の二側面は同じ頂点経路を共有する。
方針：元証人の同じ端点式を使う。規約：元全経路を保持。
使われ方：元四境界比較の接合。 -/
lemma dgOdotMilnorOuterUpperLeftHomotopy_path :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterTopHomotopy R d h).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterLeftHomotopy R d h).h :=
  (dgOdotMilnorOuterZeroTopWitness R d).source_path.trans
    (dgOdotMilnorOuterZeroLeftWitness R d).target_path.symm

/-- 概要：元実外周 UpperRight の二側面は同じ頂点経路を共有する。
方針：元証人の同じ端点式を使う。規約：元全経路を保持。
使われ方：元四境界比較の接合。 -/
lemma dgOdotMilnorOuterUpperRightHomotopy_path :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterTopHomotopy R d h).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (dgOdotMilnorOuterRightHomotopy R d h).h :=
  (dgOdotMilnorOuterZeroTopWitness R d).target_path.trans
    (dgOdotMilnorOuterProjectionWitness R d h).target_path.symm

/-- 概要：元実外周と元絶対 LT 外周の四境界全比較は同じ四頂点経路を共有する。
方針：元包含・商の自然性と元零側面の全比較を同時に束ねる。
規約：元始域の増大屋根・実 resolved 商を保持。使われ方：外周全図式の接合。 -/
def dgOdotMilnorOuterSquareFrameComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (dgOdotMilnorActualOuterDiagram R d h).square) where
  bottom := dgOdotMilnorOuterBottomHomotopy R d h
  right := dgOdotMilnorOuterRightHomotopy R d h
  left := dgOdotMilnorOuterLeftHomotopy R d h
  top := dgOdotMilnorOuterTopHomotopy R d h
  lower_left := dgOdotMilnorOuterLowerLeftHomotopy_path R d h
  lower_right := dgOdotMilnorOuterLowerRightHomotopy_path R d h
  upper_left := dgOdotMilnorOuterUpperLeftHomotopy_path R d h
  upper_right := dgOdotMilnorOuterUpperRightHomotopy_path R d h
  bottom_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _
    (dgOdotMilnorOuterBottomHomotopy_isInvertible R d h)
  right_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _
    (dgOdotMilnorOuterRightHomotopy_isInvertible R d h)
  left_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _
    (dgOdotMilnorOuterLeftHomotopy_isInvertible R d h)
  top_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _
    (dgOdotMilnorOuterTopHomotopy_isInvertible R d h)
end SerrePositivity.KST.SConstruction
