module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceRoofNuEdges
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRelativeSourceRoof
public import SerrePositivity.KST.LocalizingInvariants.HorizontalEquivalencePullback
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PullbackPasting

/-!
概要：元 cell 始域から同じ核への実零化比較面の不変量像は pullback。
方針：下辺の指定 ν 同値と上二頂点の実零性を使い、Sp 正本の判定を適用する。
規約：実 S 面の全単体を保持し、LT の全長方形の認証とは区別する。
使われ方：増大屋根を使う始域比較で実零化面を交換する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：実始域比較面の上二頂点は元の二つの全対象商。
方針：同じ四辺の両垂直辺の終点を読む。
規約：任意の零圏へ置き換えない。使われ方：不変量の同じ上二零頂点。 -/
lemma dgOdotMilnorSourceKernelNullSquare_zero_vertices :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorSourceKernelNullSquare R d) 0 1 =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorSourceCellInput R d)) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorSourceKernelNullSquare R d) 1 1 =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d)) := by
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (dgOdotMilnorSourceKernelNullSquare R d)
    let e : (dgKInputInfinity.{u, u + 1} R).Edge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorSourceCellInput R d))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorSourceCellInput R d))) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorSourceCellInput R d))
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceKernelNullSquare R d =
        SSet.yonedaEquiv.symm e.edge :=
      (dgOdotMilnorSourceKernelNullSquare_edges R d).2.2.1
    rw [he, Equiv.apply_symm_apply, e.tgt_eq] at h
    exact h.symm
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (dgOdotMilnorSourceKernelNullSquare R d)
    let e : (dgKInputInfinity.{u, u + 1} R).Edge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceKernelNullSquare R d =
        SSet.yonedaEquiv.symm e.edge :=
      (dgOdotMilnorSourceKernelNullSquare_edges R d).2.1
    rw [he, Equiv.apply_symm_apply, e.tgt_eq] at h
    exact h.symm

variable {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}

/-- 概要：実比較面の上二頂点は同じ不変量で実零頂点になる。
方針：Sp の同じ全対象商の Perf 零性と不変量の零保存を使用する。
規約：元の零角の ν 像を保つ。使われ方：同じ実上辺の可逆性。 -/
lemma dgOdotMilnorSourceKernelNullSquare_value_top_zero (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
        (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R ≫ E) 0 1) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
        (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R ≫ E) 1 1) := by
  constructor
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (E.app _ ((dgKInputPerfectNu R).app _
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorSourceKernelNullSquare R d) 0 1)))
    rw [(dgOdotMilnorSourceKernelNullSquare_zero_vertices R d).1, dgKInputPerfectNu_vertex]
    apply hE.preservesZero
    exact dgFixedNullInput_isZeroCategory R _
  · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (E.app _ ((dgKInputPerfectNu R).app _
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorSourceKernelNullSquare R d) 1 1)))
    rw [(dgOdotMilnorSourceKernelNullSquare_zero_vertices R d).2, dgKInputPerfectNu_vertex]
    apply hE.preservesZero
    exact dgFixedNullInput_isZeroCategory R _

/-- 概要：実始域比較面の下辺は同じ不変量で可逆。
方針：元の固定 ν 比較の可逆性を同じ関手で写す。
規約：実下辺の全一単体を保つ。使われ方：実面の pullback 判定。 -/
lemma dgOdotMilnorSourceKernelNullSquare_value_bottom_invertible
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow
      (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R ≫ E)) := by
  exact (dgOdotMilnorSourceKernelNullSquare_perfect_bottom_invertible R d h).map E

/-- 概要：同じ増大屋根の始域比較面は全 Cat^perf 局所化不変量で pullback。
方針：下辺の指定同値と上二零頂点から Sp の水平可逆辺判定を適用する。
規約：元の実 S 面と全二胞体を保持する。使われ方：始域回収と零化面の貼合せ。 -/
theorem dgOdotMilnorSourceKernelNullSquare_value_isPullback
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgOdotMilnorSourceKernelNullSquare R d ≫ dgKInputPerfectNu R ≫ E) := by
  apply isPullbackSquare_of_horizontal_invertible
  · exact dgOdotMilnorSourceKernelNullSquare_value_bottom_invertible R d h
  · have hz := dgOdotMilnorSourceKernelNullSquare_value_top_zero R d hE
    exact hz.1.isZeroHo.isIso hz.2.isZeroHo _

/-- 概要：実核零化面の認証があれば同じ始域比較長方形の外面も pullback。
方針：証明済みの始域比較面と同じ右面を Sp 正本の貼合せへ渡す。
規約：右面の未供給の認証は明示し、上下の元の実合成三角形を保持する。
使われ方：元 cell 始域へ戻る完備化付き実面の認証。 -/
theorem dgOdotMilnorSourceNullRectangle_value_outer_isPullback
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hE : IsPerfectLocalizingInvariant E)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R ≫ E)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare
      ((dgOdotMilnorSourceNullRectangle R d).diagram ≫ dgKInputPerfectNu R ≫ E) 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorSourceNullRectangle R d).diagram 2 ≫ dgKInputPerfectNu R ≫ E)
    rw [(dgOdotMilnorSourceNullRectangle R d).left_eq]
    exact dgOdotMilnorSourceKernelNullSquare_value_isPullback R d h hE
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorSourceNullRectangle R d).diagram 0 ≫ dgKInputPerfectNu R ≫ E)
    rw [(dgOdotMilnorSourceNullRectangle R d).right_eq]
    exact hr

end SerrePositivity.KST.SConstruction
