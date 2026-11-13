module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGInvertingRoofTerminalEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGInvertingHomActionFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientHomRoofRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.WeakRoofDescentFamilyEvaluation

/-! # 任意族の屋根評価と商 Hom 作用の全選択空間上の比較

概要：任意標的の同じ全体評価を使い、有限商 Hom 図式の実屋根表示と全作用族を比較する。
方針：実屋根比較ホモトピーと全体評価の実ホモトピーを、全パラメータ降下比較へ代入する。
規約：全体評価は全パラメータ族で共有できる。使われ方：任意標的の合成評価族との接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定実屋根族と商 Hom 族の実比較から、全降下選択空間上の同じ評価比較を得る。 -/
def dgInvertingHomActionFamilyEvaluationIso (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) {K : SSet.{max u v}}
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (HQ : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofTerminalEvaluationMap A D P x F
          (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) C))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentActionFamilyEvaluationIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y) a b
    (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofTerminalEvaluationMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) C) HQ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofTerminalEvaluationFamilyHomotopy A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) C (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F))

/-- 指定商 Hom 族の実屋根表示と、同じ全体評価を用いた全降下選択空間上の関手同型。 -/
structure DGInvertingHomFamilyEvaluation (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) {K : SSet.{max u v}}
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) where
  roofFamily : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y
  comparison : SSet.Homotopy (roofFamily ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)
  evaluationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (roofFamily ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofTerminalEvaluationMap A D P x F
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) C)))

/-- 同じ全体評価を固定したまま、任意の有限商 Hom 図式を全選択空間上で実評価と比較する。 -/
theorem dgInvertingHomFamilyEvaluation_nonempty (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) {K : SSet.{max u v}} [K.Finite]
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    Nonempty (DGInvertingHomFamilyEvaluation A D P x y F C b) := by
  obtain ⟨a, ⟨HQ⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientHomFinite_actualRoofLift A D P hP x y b
  exact ⟨⟨a, HQ, dgInvertingHomActionFamilyEvaluationIso A D P x y F C a b HQ⟩⟩

/-- 任意の反転関手と有限商 Hom 図式は、共有可能な全体評価と全パラメータ実比較を持つ。 -/
theorem dgInvertingHomFamilyEvaluation_exists (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) {K : SSet.{max u v}} [K.Finite]
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    ∃ C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)),
      Nonempty (DGInvertingHomFamilyEvaluation A D P x y F C b) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofTerminalEvaluation_nonempty A D P x F hF
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  exact ⟨C, dgInvertingHomFamilyEvaluation_nonempty A D P hP x y F C b⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
