module
public import SerrePositivity.KST.SConstruction.PastingOuterRightVertexEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：始域屋根長方形の左の二水平辺が可逆なら、外周と右面を全図式同型で比較する。
方針：元全長方形の既存ホモトピーを四頂点で判定する。
規約：元両四角形の全単体を保持。使われ方：同じ厚平坦核に戻す外周比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X] (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)

/-- 概要：元長方形の外周から右面への全ホモトピーは左二水平辺が可逆なら可逆。
方針：左二成分と固定右二成分の四頂点で元全関手辺を判定する。
規約：別のホモトピーは選択しない。使われ方：始域屋根の全比較。 -/
lemma pastingOuterRightHomotopy_isInvertible
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  rintro ⟨p, q⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
  fin_cases i
  · fin_cases j
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (pastingOuterRightVertexEdge_bottom F)).mpr hb
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (pastingOuterRightVertexEdge_top F)).mpr ht
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (pastingOuterRightVertexEdge_fixed F j)).mpr
    change IsIso (Truncated.HomotopyCategory.homMk
      (Truncated.Edge.id (X := (truncation 2).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 j)))
    exact (congrArg (fun f => IsIso f)
      (Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 j))).mpr (by infer_instance)

/-- 概要：元長方形の外周と右面の全比較を同じ元ホモトピーから構成する。
方針：同じ辺の類をその可逆性で同型にする。規約：指定全ホモトピーを保持。
使われ方：厚平坦核を始点とする実核面への外周比較の輸送。 -/
def pastingOuterRightComparison
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) :=
  @asIso _ _ _ _ (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F)))
      (pastingOuterRightHomotopy_isInvertible F hb ht)
end SerrePositivity.KST.SConstruction
