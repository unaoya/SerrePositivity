module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGPointCosliceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGCoherentCosliceTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComparisonEquivalence
/-!
概要：同じ線形 Hom の coslice 比較を、dg nerve の実 coslice fiber へ渡す。
方針：coherent 比較関手の全 fiber 射と既存の輸送正方形を合成する。
規約：各辺の実輸送を保持し、点ごとの同値だけで自然性を代用しない。
使われ方：線形ホモロジーチャートと native 評価の実辺作用の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 標準線形 Hom の同じ比較を、比較関手の実像上の dg coslice fiber へ送る。 -/
def dgBarCompactCoherentCosliceComparison (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)

lemma dgBarCompactCoherentCosliceComparison_isQCatEquivalence
    (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentCosliceComparison R D x y) := by
  let : Quasicategory (SimplicialNerve (ClosedCategory R D)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (_root_.SerrePositivity.DifferentialGraded.ClosedCategory R D)
  have h₁ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison_homotopyEquivalence x y).isQCatEquivalence
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap_equivalence_iff_pinchedHomMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)).mpr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_fullyFaithful (R := R) (D := D) _ _)
  exact h₁.comp h₂

/-- 同じ線形係数の実射と、dg nerve 内の同じ辺の輸送との全比較。 -/
def dgBarCompactCoherentCosliceComparison_transportIso
    {I : Type u} [Category.{u} I] (F : I ⥤ ClosedCategory R D)
    (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{v, u}).map
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) ≫
        dgBarCompactCoherentCosliceComparison R D x (F.obj j))
      (dgBarCompactCoherentCosliceComparison R D x (F.obj i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)))) := by
  let : Quasicategory (SimplicialNerve (ClosedCategory R D)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (ClosedCategory R D)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftFibrationSquareTransportIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm a))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (q.app (Opposite.op ⦋0⦌) a)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCoslicePostcomp q a) q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCoslicePostcomp_projection q a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f))
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCoslicePostcomp_fiber q a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj j)),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCoslicePostcomp_fiber q a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i))] at h
  have H := ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentCosliceFiberComparison_transportIso F x f).postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap q a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj j)))).trans
      (h.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x (F.obj i)))
  simpa only [dgBarCompactCoherentCosliceComparison, Category.assoc] using H

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
