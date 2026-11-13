module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceRoofNuEdges
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuSourceSquare
public import SerrePositivity.KST.SConstruction.PastingOuterRightComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：元 cell 始域外面から厚平坦核を始域とする実核面への Cat^perf 全比較。
方針：元始域比較長方形の全ホモトピーと同じ二水平 ν 同値を使う。
規約：元両面の全単体と元増大屋根を保持。使われ方：LT 外周認証の厚核面への輸送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元実外周と同じ厚核零化面は全 Cat^perf 図式として同型。
方針：元長方形の外周から右面への既存ホモトピーを同じ二水平辺で可逆にする。
規約：四辺だけで代用せず全四角形を保持。使われ方：厚核を始点とする外周認証。 -/
def dgOdotMilnorSourceOuterToKernelPerfectComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) := by
  let F := (dgOdotMilnorSourceNullRectangle R d).diagram
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F ≫ dgKInputPerfectNu R) 2)) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F) 2 ≫ dgKInputPerfectNu R))
    rw [(dgOdotMilnorSourceNullRectangle R d).left_eq]
    exact dgOdotMilnorSourceKernelNullSquare_perfect_bottom_invertible R d h
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F ≫ dgKInputPerfectNu R) 2)) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F) 2 ≫ dgKInputPerfectNu R))
    rw [(dgOdotMilnorSourceNullRectangle R d).left_eq]
    exact dgOdotMilnorSourceKernelNullSquare_perfect_top_invertible R d
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (pastingOuterRightComparison (F ≫ dgKInputPerfectNu R) hb ht)
    rfl (congrArg (fun k => k ≫ dgKInputPerfectNu R)
      (dgOdotMilnorSourceNullRectangle R d).right_eq)
end SerrePositivity.KST.SConstruction
