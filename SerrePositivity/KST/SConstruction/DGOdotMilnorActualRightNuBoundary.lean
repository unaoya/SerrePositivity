module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualSRectangle
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEdgeDiagram
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero

/-!
概要：共通実 S 長方形の右面の四辺と零角を、同じ Cat^perf ν 像で回収する。
方針：元実右面の厳密回収と元全一単体の ν 回収を合成する。
規約：元 V と元全対象商を保持し、全四角形比較の完成とは数えない。
使われ方：ActualRectangleInput.rightComparison の実側の指定境界。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma recoverZeroVertex {X : SSet.{v}}
    {F : (Δ[1] ⊗ Δ[1] : SSet.{v}) ⟶ X} {a b : X _⦋0⦌}
    (e : X.Edge a b) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm e.edge) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1 = b := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target F
  rw [h, Equiv.apply_symm_apply, e.tgt_eq] at ht
  exact ht.symm

private lemma mapPerfectBoundary (R : Type u) [CommRing R]
    (F G : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R)
    (hFG : F = G) (a : (Δ[1] : SSet.{u + 2}) ⟶ (Δ[1] ⊗ Δ[1]))
    {A B : PerfDGInput.{u, u + 1} R} (f : A ⟶ B)
    (h : a ≫ G = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
    a ≫ F ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgKInputNuMap R f)
        (dgKInputStableValue_isIdempotentComplete R A)
        (dgKInputStableValue_isIdempotentComplete R B)).edge := by
  rw [hFG, ← Category.assoc, h]
  exact dgKInputPerfectNu_edge_diagram R f

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "VInput" => dgIdentityHomGluingNullInput R (U)
local notation "i" => dgIdentityHomGluingNullInputMap R (U)
local notation "q" => dgIdentityHomGluingDifferenceInputMap R (U)
local notation "N" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ dgOdotMilnorActualRectangleDiagram R d

/-- 概要：共通長方形の実右面の零角は元 V の全対象商。
方針：同じ実零化面の左辺の終点を回収する。
規約：元の頂点の等号。使われ方：固定 ν の零角証明。 -/
lemma dgOdotMilnorActualRight_zero_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (N) 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (VInput)) := by
  exact (congrArg (fun F => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1)
    (dgOdotMilnorActualRectangleDiagram_right R d)).trans
      (recoverZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := VInput)))
        (dgIdentityHomGluingNullDomainSquare_edges R (U)).2.2.1)

/-- 概要：共通実右面の同じ固定 ν 零角は零 Cat^perf 圏。
方針：元全対象商に Sp 正本の Perf 零性を適用する。
規約：各対象の収縮だけで代用しない。使われ方：実右面の零角認証。 -/
lemma dgOdotMilnorActualRight_perfect_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((N) ≫ dgKInputPerfectNu R) 0 1)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (N) 0 1)))
  rw [dgOdotMilnorActualRight_zero_vertex, dgKInputPerfectNu_vertex]
  exact dgFixedNullInput_isZeroCategory R (VInput)

/-- 概要：実右面の元包含辺を Cat^perf の全区間として回収する。
方針：元右面回収・元四辺・固定 ν 全一単体の回収を合成する。
規約：V の元包含を保持。使われ方：指定包含境界。 -/
lemma dgOdotMilnorActualRight_nu_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (N) ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgKInputNuMap R (i))
        (dgKInputStableValue_isIdempotentComplete R (VInput))
        (dgKInputStableValue_isIdempotentComplete R
          (dgIdentityHomGluingGluingInput R (U)))).edge := by
  exact mapPerfectBoundary R _ _ (dgOdotMilnorActualRectangleDiagram_right R d)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge (i) (dgIdentityHomGluingNullDomainSquare_edges R (U)).1

/-- 概要：実右面の元 cone 差辺を Cat^perf の全区間として回収する。
方針：元右面回収・元四辺・固定 ν 全一単体の回収を合成する。
規約：元の実 cone 差を保持。使われ方：指定商境界。 -/
lemma dgOdotMilnorActualRight_nu_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (N) ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgKInputNuMap R (q))
        (dgKInputStableValue_isIdempotentComplete R
          (dgIdentityHomGluingGluingInput R (U)))
        (dgKInputStableValue_isIdempotentComplete R
          (dgIdentityHomGluingDifferenceInput R (U)))).edge := by
  exact mapPerfectBoundary R _ _ (dgOdotMilnorActualRectangleDiagram_right R d)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (q) (dgIdentityHomGluingNullDomainSquare_edges R (U)).2.1

/-- 概要：実右面の元全対象商への辺を Cat^perf の全区間として回収する。
方針：同じ実右面の左辺を固定 ν の元辺回収へ渡す。
規約：元零角と元商包含を保持。使われ方：指定零角の始域側境界。 -/
lemma dgOdotMilnorActualRight_nu_zero_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (N) ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgFixedNullLeft R (A := VInput)))
        (dgKInputStableValue_isIdempotentComplete R (VInput))
        (dgKInputStableValue_isIdempotentComplete R
          (dgFixedNullInput R (VInput)))).edge := by
  exact mapPerfectBoundary R _ _ (dgOdotMilnorActualRectangleDiagram_right R d)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge _ (dgIdentityHomGluingNullDomainSquare_edges R (U)).2.2.1

/-- 概要：実右面の元全対象商からの延長辺を Cat^perf の全区間として回収する。
方針：同じ対象別収縮の商延長と固定 ν の元辺回収を使う。
規約：元全関手の自然収縮は要求しない。使われ方：指定零角の終域側境界。 -/
lemma dgOdotMilnorActualRight_nu_zero_extension :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (N) ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgFixedNullTop R (dgIdentityHomGluingNullContracted R (U))))
        (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (VInput)))
        (dgKInputStableValue_isIdempotentComplete R
          (dgIdentityHomGluingDifferenceInput R (U)))).edge := by
  exact mapPerfectBoundary R _ _ (dgOdotMilnorActualRectangleDiagram_right R d)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge _ (dgIdentityHomGluingNullDomainSquare_edges R (U)).2.2.2

end SerrePositivity.KST.SConstruction
