module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityNullSquare
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero

/-!
概要：恒等 Hom gluing の実零化面を、同じ固定 ν と Cat^perf の全図式へ写す。
方針：元の全対象商の零性と、四辺の全一単体回収を使用する。
規約：同じ面と零角を保持し、恒等 lax 差との比較・列認証とは区別する。
使われ方：LT 長方形の右面を完備化付き接続口へ渡す境界データ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：実零角は同じ小 Perf 基底の全対象商そのもの。
方針：同じ左辺の終点を読む。規約：零圏へ置換しない。
使われ方：固定 ν の零角認証。 -/
lemma dgOdotMilnorIdentityNullSquare_zero_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorIdentityNullSquare R d) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorIdentityBaseInput R d)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (dgOdotMilnorIdentityNullSquare R d)
  let le : (dgKInputInfinity.{u, u + 1} R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorIdentityBaseInput R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (dgOdotMilnorIdentityBaseInput R d))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorIdentityBaseInput R d))
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorIdentityNullSquare R d =
      SSet.yonedaEquiv.symm le.edge := (dgOdotMilnorIdentityNullSquare_edges R d).2.2.1
  rw [hl, Equiv.apply_symm_apply, le.tgt_eq] at h
  exact h.symm

/-- 概要：同じ実零角の固定 ν 像は零安定圏。
方針：Sp 正本の全対象商 Perf 零性を使用する。
規約：対象別収縮の存在だけでは代用しない。使われ方：実面の零角条件。 -/
lemma dgOdotMilnorIdentityNullSquare_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputNu R) 0 1)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorIdentityNullSquare R d) 0 1)))
  rw [dgOdotMilnorIdentityNullSquare_zero_vertex, dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
  exact dgFixedNullInput_isZeroCategory R _

/-- 概要：同じ全単体の Cat^perf 像も同じ零角を持つ。
方針：固定 ν との厳密一致を使用する。
規約：完備化後射影の認証とは別。使われ方：完備化付き実面の零角。 -/
lemma dgOdotMilnorIdentityNullSquare_perfect_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) 0 1)) := by
  have h := dgOdotMilnorIdentityNullSquare_zero R d
  rw [← dgKInputPerfectNu_inclusion R] at h
  exact h

/-- 概要：同じ実面の下辺の固定 ν 像は元の対角の完全射。
方針：四辺固定式を全一単体回収に接続する。
規約：元の strict 対角を保持する。使われ方：恒等 lax 対角との全比較。 -/
lemma dgOdotMilnorIdentityNullSquare_nu_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow
        (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d))).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorIdentityDiagonalInputMap R d)).edge) = _
  exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputNu_edge R (dgOdotMilnorIdentityDiagonalInputMap R d))

/-- 概要：同じ実面の右辺の固定 ν 像は元の実 cone 差の完全射。
方針：元の差の四辺固定式と全一単体回収を使う。
規約：普遍差との全比較は別途必要。使われ方：同じ差の指定境界。 -/
lemma dgOdotMilnorIdentityNullSquare_nu_difference :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow
        (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d))).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorIdentityDifferenceInputMap R d)).edge) = _
  exact congrArg (fun x : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputNu_edge R (dgOdotMilnorIdentityDifferenceInputMap R d))

end SerrePositivity.KST.SConstruction
