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
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper

/-- 概要：元二脚の両射影付き全比較と、元角評価を保持する全 cone 差比較の未供給型。
方針：小 corner の実包含後評価を指定し、元 cone 全関手を lax 差に照合する。
規約：対角は同じ native 対角と比較の合成で保持。存在証明ではない。
使われ方：D2 の元二脚側供給に必要な全関手同型の正確な型。 -/
structure DGOdotMilnorOriginalLaxConeComparisonInput where
  laxComparison : DGOdotMilnorOriginalLaxComparisonInput R d
  cornerEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (DGOdotCorner R d)))
    (dgKInputStableValue R (dgOdotCornerInput R d)).obj
  cornerYoneda : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (DGOdotCorner R d)) ≫ cornerEvaluation.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectSquareCornerInclusion R (A) (B) (C) (E) (L) (G) (p) (q)) ≫
      (dgOdotMilnorCornerPerfectValueEquivalence R d).hom)
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      (laxComparison.gluing.hom ≫
        (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotTargetFunctor R d) ≫ cornerEvaluation.hom)
end SerrePositivity.KST.SConstruction
