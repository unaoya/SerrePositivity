module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismSideHomotopies

/-!
概要：同じ元上下二胞体の三面を、指定比較側面の元辺に厳密照合する。
方針：既存の標準二三角形の面等号と元二胞体の Yoneda 回収を使う。
規約：元二胞体を取り替えない。使われ方：実側境界の二端点の元面回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元実二胞体の最初の辺は元左辺または元包含辺。
方針：同じ標準三角形の最初の面を回収する。
規約：元全一単体の等号。使われ方：元比較側境界の始端照合。 -/
lemma dgOdotMilnorNuNullPrismTriangle_first_actual (j : Fin 2) :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j) =
      ![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge] j ≫
        dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  change stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)) = _
  rw [Equiv.symm_apply_apply]
  fin_cases j
  · change stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫
      dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge]
  · change stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫
      dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge]


/-- 概要：元絶対二胞体の最初の辺は元標準左辺または元包含辺。
方針：同じ元絶対提示の最初の面を回収する。
規約：元全一単体の等号。使われ方：元比較側境界の終端照合。 -/
lemma dgOdotMilnorNuNullPrismTriangle_first_absolute (j : Fin 2) :
    stdSimplex.δ (2 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j) =
      ![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge] j ≫
        perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) := by
  change stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))) = _
  rw [Equiv.symm_apply_apply]
  fin_cases j
  · change stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge]
  · change stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge]


/-- 概要：元実二胞体の最後の辺は元上辺または元商辺。
方針：同じ標準三角形の最後の面を回収する。
規約：元全一単体の等号。使われ方：元比較側境界の始端照合。 -/
lemma dgOdotMilnorNuNullPrismTriangle_last_actual (j : Fin 2) :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j) =
      ![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge] j ≫
        dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  change stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)) = _
  rw [Equiv.symm_apply_apply]
  fin_cases j
  · change stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫
      dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge]
  · change stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫
      dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge]


/-- 概要：元絶対二胞体の最後の辺は元標準上辺または元指定商辺。
方針：同じ元絶対提示の最後の面を回収する。
規約：元全一単体の等号。使われ方：元比較側境界の終端照合。 -/
lemma dgOdotMilnorNuNullPrismTriangle_last_absolute (j : Fin 2) :
    stdSimplex.δ (0 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j) =
      ![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge] j ≫
        perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) := by
  change stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))) = _
  rw [Equiv.symm_apply_apply]
  fin_cases j
  · change stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge]
  · change stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge]


/-- 概要：元実二胞体の対角面は同じ実四角形の共有対角。
方針：元標準二三角形の同じ対角面等号を使う。
規約：元全一単体の等号。使われ方：共有比較側面の始端照合。 -/
lemma dgOdotMilnorNuNullPrismTriangle_diagonal_actual (j : Fin 2) :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  change stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

/-- 概要：元絶対二胞体の対角面は同じ絶対四角形の共有対角。
方針：同じ元絶対提示の共有面等号を使う。
規約：元全一単体の等号。使われ方：共有比較側面の終端照合。 -/
lemma dgOdotMilnorNuNullPrismTriangle_diagonal_absolute (j : Fin 2) :
    stdSimplex.δ (1 : Fin 3) ≫
        SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) := by
  change stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

end SerrePositivity.KST.SConstruction
