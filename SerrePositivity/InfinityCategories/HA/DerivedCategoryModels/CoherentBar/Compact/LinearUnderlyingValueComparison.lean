module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CoherentCosliceEvaluationComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CosliceUnderlyingValueNaturality
/-!
概要：線形 Hom の同じ係数図式と、native 基礎空間値の実辺作用を比較する。
方針：coherent coslice と始点固定 Tw の二つの輸送比較を合成する。
規約：係数の射と元の coherent 辺を保持し、strict 図式への置換は行わない。
使われ方：評価コホモロジーチャートを元の native 図式の実脚へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 比較関手の同じ像を始点とする native 基礎空間関手。 -/
def dgBarCompactCoherentUnderlyingValueFunctor (x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUnderlyingValueFunctor
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))

/-- 同じ線形 Hom から、同じ基礎空間関手の持ち上げた実値への比較。 -/
def dgBarCompactLinearUnderlyingValueComparison (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :=
  (SSet.uliftFunctor.{max u v + 1, max u v}).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentCosliceComparison R D x y) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCosliceUnderlyingValueComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y))

lemma dgBarCompactLinearUnderlyingValueComparison_isQCatEquivalence
    (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactLinearUnderlyingValueComparison R D x y) := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentCosliceComparison_isQCatEquivalence R D x y).ulift.{max u v, max u v + 1}
  exact h.comp (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCosliceUnderlyingValueComparison_isQCatEquivalence _ _)

/-- 全係数の実射と、その native 基礎空間値での実辺作用の比較。 -/
def dgBarCompactLinearUnderlyingValueComparison_transportIso
    {I : Type u} [Category.{u} I] (F : I ⥤ ClosedCategory R D)
    (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max u v + 1, max u v}).map
          ((SSet.uliftFunctor.{v, u}).map
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f)) ≫
        dgBarCompactLinearUnderlyingValueComparison R D x (F.obj j))
      (dgBarCompactLinearUnderlyingValueComparison R D x (F.obj i) ≫
        (SSet.uliftFunctor.{max u v + 1, max u v}).map
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
            ((SSet.Edge.ofTruncated
              (X := (SSet.uliftFunctor.{max u v + 1, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))
              (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max u v, max u v + 1}
                ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).map
                  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))))).map
                    (dgBarCompactCoherentUnderlyingValueFunctor R D x)))) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)
  let a := q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)
  have h₁ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentCosliceComparison_transportIso R D F x f).ulift.{max u v, max u v + 1}
  have h₁' := h₁.postcomp (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCosliceUnderlyingValueComparison a
    (q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj j))))
  have h₂ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCosliceUnderlyingValueComparison_transportIso a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).map q)).precomp
      ((SSet.uliftFunctor.{max u v + 1, max u v}).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentCosliceComparison R D x (F.obj i)))
  dsimp only [a, q] at h₁' h₂
  simp only [Functor.map_comp, Category.assoc] at h₁' h₂
  dsimp only [dgBarCompactLinearUnderlyingValueComparison,
    dgBarCompactCoherentUnderlyingValueFunctor]
  rw [Category.assoc]
  exact h₁'.trans h₂


end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
