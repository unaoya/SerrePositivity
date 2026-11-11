module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFunctorImage
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostCoordinates

/-!
概要：実際の weighted coslice 比較は豊穣関手による後合成と厳密に可換。
方針：始点の表示を正規化し、元の cone simplex の後合成の等式を全次数で使う。
規約：同値の逆の選択で比較を置き換えない。
使われ方：weighted nerve と反転係数の unstraightening の共同実現。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions


variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 豊穣関手の coherent nerve は、始点の Yoneda 射を像の標準頂点の Yoneda 射へ写す。 -/
lemma coherentNerveMap_point_diagram (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (R.obj x)) := by
  rw [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]

/-- 元の coherent coslice の錐を豊穣関手で写し、同じ始点の標準表示へ正規化する。 -/
def coherentCosliceFunctorImage (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (R.obj x))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R) ≫
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (coherentNerveMap_point_diagram R x))

/-- 正規化した後合成は、元の錐の射そのものへの後合成。 -/
lemma coherentCosliceFunctorImage_app_val (R : EnrichedFunctor SSet.{u} C D) (x : C)
    {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))) _⦋n⦌) :
    ((coherentCosliceFunctorImage R x).app (Opposite.op ⦋n⦌) s).val =
      s.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R := by
  change ((eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (coherentNerveMap_point_diagram R x))).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)).app _ s)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder_eqToHom_app_val (coherentNerveMap_point_diagram R x)]
  rfl

/-- 同じ coslice の後合成は、底への射影を元の coherent nerve の射で被覆する。 -/
lemma coherentCosliceFunctorImage_projection (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    coherentCosliceFunctorImage R x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (R.obj x))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R := by
  rw [coherentCosliceFunctorImage, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnder_eqToHom_projection (coherentNerveMap_point_diagram R x)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection _ _

/-- 元の全 weighted coslice 比較は、全係数単体で豊穣関手の後合成と厳密に可換。 -/
lemma weightedCosliceComparison_functorImage {I : Type u} [SmallCategory I]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x ≫ coherentCosliceFunctorImage R x =
      (SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedHomFunctorImage F R x) SSet.opFunctor)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((coherentCosliceFunctorImage R x).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x).app _ s)).val = _
  rw [coherentCosliceFunctorImage_app_val]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x s.down.2)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (show (SimplicialNerve D) _⦋n + 1⦌ from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x s.down.2).comp SSet R) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeSimplex_functorImage]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
