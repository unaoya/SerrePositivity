module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceNullRectangle
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRelativeSourceRoof
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectMap

/-!
概要：元始域比較面の二水平辺の Cat^perf ν 像は同じ全一単体のまま可逆となる。
方針：下辺には元 dg 準同値を、上辺には同じ二全対象商の零頂点比較を使う。
規約：元実 S 面と辺を保持。使われ方：外周から厚核面への全図式同型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：実始域比較面の下辺の Cat^perf ν 像は元準同値により可逆。
方針：固定 ν の元一単体回収と元実辺の式を使う。
規約：元始域増大屋根の辺を保持。使われ方：全外周比較の左下成分。 -/
lemma dgOdotMilnorSourceKernelNullSquare_perfect_bottom_invertible
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow
      (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R)) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (dgOdotMilnorSourceKernelInputMap R d)).map (dgKInputPerfectNu R)).toTruncated :=
    dgKInputPerfectNu_map_isIso_of_isQCatEquivalence R
      (dgOdotMilnorSourceKernelInputMap R d) (dgOdotMilnorSourceKernelNu_isQCatEquivalence R d h)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _) (f := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow
    (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R)) ?_).mp hi
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, ← Category.assoc,
    (dgOdotMilnorSourceKernelNullSquare_edges R d).1]
  simp only [SSet.yonedaEquiv_comp]
  rfl

/-- 概要：実始域比較面の上辺の Cat^perf ν 像は元二全対象商の比較として可逆。
方針：元の商延長辺と同じ二零角の指定同型を照合する。
規約：上辺全体を保持。使われ方：全外周比較の左上成分。 -/
lemma dgOdotMilnorSourceKernelNullSquare_perfect_top_invertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow
      (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R)) := by
  have hi := dgKFixedNullPerfectNuMap_isInvertible R
    (dgOdotMilnorSourceCellInput R d) (dgOdotMilnorFlatKernelInput R d)
    (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d))
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _) (f := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow
    (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R)) ?_).mp hi
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge, ← Category.assoc,
    (dgOdotMilnorSourceKernelNullSquare_edges R d).2.2.2]
  simp only [SSet.yonedaEquiv_comp]
  rfl
end SerrePositivity.KST.SConstruction
