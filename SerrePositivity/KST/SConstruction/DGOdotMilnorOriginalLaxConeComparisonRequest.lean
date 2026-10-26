module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxComparisonRequest
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCornerPerfectValueEquivalence
public import SerrePositivity.KST.SConstruction.DGOdotTargetFunctor

/-!
概要：元二脚の lax 全比較について、元 corner 評価と同じ実 cone 差も保持する供給型。
方針：既存の両射影付き比較に、元小 corner の Yoneda 評価と実 cone 全関手を加える。
規約：この供給型の存在は未証明。元の二脚比較の公開型は変更しない。
使われ方：D2 へ依頼する元二脚側の全差比較と、元角値の選択の固定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgAlgebraCategory R d.source
local notation "B" => dgAlgebraCategory R d.left
local notation "C" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "L" => dgAlgebraMap R d.top
local notation "G" => dgAlgebraMap R d.side
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper

/-- 概要：元二脚の両射影付き全比較と、元角評価を保持する全 cone 差比較の未供給型。
方針：小 corner の実包含後評価を指定し、元 cone 全関手を lax 差に照合する。
規約：対角は同じ native 対角と比較の合成で保持。存在証明ではない。
使われ方：D2 の元二脚側供給に必要な全関手同型の正確な型。 -/
structure DGOdotMilnorOriginalLaxConeComparisonInput where
  laxComparison : DGOdotMilnorOriginalLaxComparisonInput R d
  cornerEvaluation : QCatEquivalence
    (dgNerve R (PerfectDGModule R (DGOdotCorner R d)))
    (dgKInputStableValue R (dgOdotCornerInput R d)).obj
  cornerYoneda : FunctorIso
    (dgNerve.map (dgPerfectYoneda R (DGOdotCorner R d)) ≫ cornerEvaluation.hom)
    (dgNerve.map (dgSmallPerfectSquareCornerInclusion R (A) (B) (C) (E) (L) (G) (p) (q)) ≫
      (dgOdotMilnorCornerPerfectValueEquivalence R d).hom)
  cone : FunctorIso
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      (laxComparison.gluing.hom ≫
        (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom))
    (dgNerve.map (dgOdotTargetFunctor R d) ≫ cornerEvaluation.hom)
end SerrePositivity.KST.SConstruction
