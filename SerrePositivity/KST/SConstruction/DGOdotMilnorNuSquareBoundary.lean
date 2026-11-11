module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuVerdier
public import SerrePositivity.KST.SConstruction.DGOdotMilnorPerfectNullSquare
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence

/-!
概要：実 S 零化面の包含辺・商辺を同じ固定 ν の実 Cat^perf 辺へ照合する。
方針：元の四辺固定式と全一単体の ν 回収を使用する。
規約：商辺は構成済み完備化後射影との指定全関手同型を併用する。
使われ方：Sp の完備化付き実面認証に渡す同じ包含辺・商辺・零角。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：実 S 零化面の下辺は同じ完備化付き列の固定 ν 包含辺そのもの。
方針：四辺回収と同じ Cat^perf の全一単体回収を使用する。
規約：辺の代表や包含射を選び直さない。使われ方：Sp の包含境界。 -/
lemma dgOdotMilnorPerfectNullSquare_nu_inclusion (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgOdotMilnorNuPerfectSequence R d h).verdier.inclusion
        (dgOdotMilnorNuPerfectSequence R d h).left_complete
        (dgOdotMilnorNuPerfectSequence R d h).middle_complete).edge := by
  rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgOdotMilnorFlatKernelInputMap R d))

/-- 概要：同じ実 S 面の右辺は元の固定 ν cell 商辺そのもの。
方針：元の四辺回収と全一単体回収を使用する。
規約：実列の右射への比較は既構成の全関手同型を使用する。
使われ方：Sp の指定商境界と実完備化後射影の照合。 -/
lemma dgOdotMilnorPerfectNullSquare_nu_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgOdotMilnorCellProjectionExactMap R d)
        (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorCellInput R d))
        (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge := by
  rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgOdotMilnorCellProjectionInputMap R d))

end SerrePositivity.KST.SConstruction
