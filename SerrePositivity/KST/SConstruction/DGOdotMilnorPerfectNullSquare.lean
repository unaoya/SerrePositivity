module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorFlatKernelNullSquare
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero

/-!
概要：resolved 商の実零化面に、固定 ν の零角の証拠を付ける。
方針：既存の同じ四辺を選び、Sp の全対象商 Perf 零性を適用する。
規約：完備化後の射影に strict 局所化を要求しない。
使われ方：完備化付き相対提示で使用する実面と、その Cat^perf 像。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：同じ平坦核と resolved 商包含を持つ実零化面。
方針：証明済みの四辺固定の面を選ぶ。規約：辺を選び直さない。
使われ方：固定 S の完備化付き相対提示。 -/
def dgOdotMilnorPerfectNullSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  (exists_dgOdotMilnorFlatKernelNullSquare R d).choose

/-- 概要：実面の四辺は元の四つの厳密 dg 辺。
方針：同じ存在証明の境界を回収する。規約：全一単体での等号。
使われ方：包含・商・零角への指定境界。 -/
lemma dgOdotMilnorPerfectNullSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).edge :=
  (exists_dgOdotMilnorFlatKernelNullSquare R d).choose_spec

/-- 概要：零角は同じ平坦核の全対象商そのもの。
方針：元の左辺の終点を読む。規約：任意の零圏への置換はしない。
使われ方：固定 ν の零性判定。 -/
lemma dgOdotMilnorPerfectNullSquare_zero_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (dgOdotMilnorPerfectNullSquare R d)
  let le : (dgKInputInfinity.{u, u + 1} R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d =
      SSet.yonedaEquiv.symm le.edge := (dgOdotMilnorPerfectNullSquare_edges R d).2.2.1
  rw [hl, Equiv.apply_symm_apply, le.tgt_eq] at h
  exact h.symm

/-- 概要：同じ実零角の ν 値は零安定圏。
方針：Sp 正本の全対象商 Perf 零性を使う。規約：対象別収縮だけで代用しない。
使われ方：相対提示の零角条件を充足する。 -/
lemma dgOdotMilnorPerfectNullSquare_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R) 0 1)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d) 0 1)))
  rw [dgOdotMilnorPerfectNullSquare_zero_vertex, dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
  exact dgFixedNullInput_isZeroCategory R _

/-- 概要：同じ零角条件を全単体が同じ Cat^perf 持ち上げで保持する。
方針：元の ν との厳密一致を使う。規約：実商の完備化証拠とは区別する。
使われ方：Sp の完備化付き ofSquare の零角。 -/
lemma dgOdotMilnorPerfectNullSquare_perfect_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) 0 1)) := by
  have h := dgOdotMilnorPerfectNullSquare_zero R d
  rw [← dgKInputPerfectNu_inclusion R] at h
  exact h

/-- 概要：実面の右辺の ν 像は同じ cell 商包含の完全射。
方針：固定界面の全一単体の回収を適用する。規約：未分解商を使わない。
使われ方：resolved 屋根と相対提示の右境界。 -/
lemma dgOdotMilnorPerfectNullSquare_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorCellProjectionExactMap R d)).edge := by
  rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge) = _
  exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputNu_edge R (dgOdotMilnorCellProjectionInputMap R d))

end SerrePositivity.KST.SConstruction
