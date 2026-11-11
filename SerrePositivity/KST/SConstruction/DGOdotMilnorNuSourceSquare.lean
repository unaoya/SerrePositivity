module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuSourceVerdier
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceRoofPullback

/-!
概要：元 cell 始域の実長方形の外面を、同じ完備化付き列の境界へ接続する。
方針：元の上下合成二単体と右面・左面の全一単体を回収する。
規約：元の長方形と零角を保持し、指定商同型を厳密等号と取り違えない。
使われ方：Sp の完備化付き実面認証へ渡す具体的外面・包含辺・商辺・零角。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：同じ始域比較長方形の実外面。
方針：元の全長方形の長辺を取る。規約：別の零化面を選択しない。
使われ方：元 cell 始域を持つ完備化付き実面。 -/
def dgOdotMilnorSourceNullOuterSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (dgOdotMilnorSourceNullRectangle R d).diagram 1

/-- 概要：実外面の四辺は元の合成辺・cell 商辺・全対象商辺・合成延長。
方針：元の指定上下二単体と実貼合せの両端を読む。
規約：全一単体の厳密等号。使われ方：Sp の外面境界照合。 -/
lemma dgOdotMilnorSourceNullOuterSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorSourceNullOuterSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d ≫
          dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceNullOuterSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceNullOuterSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgFixedNullLeft R (A := dgOdotMilnorSourceCellInput R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorSourceNullOuterSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d) ≫
            dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).edge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _ 1 = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge, (dgOdotMilnorSourceNullRectangle R d).bottom_eq,
      stdSimplex.δ_comp_yonedaEquiv_symm, (dgOdotMilnorSourceNullBottomTriangle R d).d₁]
    rfl
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _ 1 = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_rightEdge, (dgOdotMilnorSourceNullRectangle R d).right_eq]
    exact (dgOdotMilnorPerfectNullSquare_edges R d).2.1
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _ 1 = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_leftEdge, (dgOdotMilnorSourceNullRectangle R d).left_eq]
    exact (dgOdotMilnorSourceKernelNullSquare_edges R d).2.2.1
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _ 1 = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge, (dgOdotMilnorSourceNullRectangle R d).top_eq,
      stdSimplex.δ_comp_yonedaEquiv_symm, (dgOdotMilnorSourceNullTopTriangle R d).d₁]
    rfl

/-- 概要：実外面の零角は元 cell 始域の同じ全対象商。
方針：同じ実左辺の終点から回収する。規約：頂点を選び直さない。
使われ方：Sp の完備化付き実面の零角認証。 -/
lemma dgOdotMilnorSourceNullOuterSquare_zero_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorSourceNullOuterSquare R d) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorSourceCellInput R d)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (dgOdotMilnorSourceNullOuterSquare R d)
  let e : (dgKInputInfinity.{u, u + 1} R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorSourceCellInput R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorSourceCellInput R d))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorSourceCellInput R d))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceNullOuterSquare R d =
      SSet.yonedaEquiv.symm e.edge := (dgOdotMilnorSourceNullOuterSquare_edges R d).2.2.1
  rw [he, Equiv.apply_symm_apply, e.tgt_eq] at h
  exact h.symm

/-- 概要：同じ実外面の固定 ν の Cat^perf 像は零角を保つ。
方針：元の全対象商の実 Perf 零性を適用する。
規約：外周の指定完備化を変更しない。使われ方：Sp の外面零角条件。 -/
lemma dgOdotMilnorSourceNullOuterSquare_perfect_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
      (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) 0 1)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorSourceNullOuterSquare R d) 0 1)))
  rw [dgOdotMilnorSourceNullOuterSquare_zero_vertex, dgKInputPerfectNu_vertex]
  exact dgFixedNullInput_isZeroCategory R _

/-- 概要：実外面の下辺の ν 像は同じ外周列の包含辺そのもの。
方針：元 S の合成辺と固定 ν の全一単体回収を使う。
規約：全関手の同型類でなく全一単体を保持する。使われ方：Sp の包含境界。 -/
lemma dgOdotMilnorSourceNullOuterSquare_nu_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuSourceInclusion R d)).edge := by
  rw [← Category.assoc, (dgOdotMilnorSourceNullOuterSquare_edges R d).1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
    (dgOdotMilnorSourceKernelInputMap R d ≫ dgOdotMilnorFlatKernelInputMap R d)).edge) = _
  exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputNu_edge R (dgOdotMilnorSourceKernelInputMap R d ≫
      dgOdotMilnorFlatKernelInputMap R d))

/-- 概要：実外面の右辺の ν 像は同じ元 cell 商辺そのもの。
方針：右面と共有する実右辺の全一単体を回収する。
規約：完備化後射影へは指定全関手同型を併用する。使われ方：Sp の商境界。 -/
lemma dgOdotMilnorSourceNullOuterSquare_nu_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorCellProjectionExactMap R d)).edge := by
  rw [← Category.assoc, (dgOdotMilnorSourceNullOuterSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge) = _
  exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputNu_edge R (dgOdotMilnorCellProjectionInputMap R d))

end SerrePositivity.KST.SConstruction
