module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeTotalFunctorImage
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictKanUnstraighteningComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveMapComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：weighted cone の全空間の後合成は、実際の Hom の同値から同値となる。
方針：元の weighted 比較の fiber 判定と、係数図式の同値を可換式で消去する。
規約：始点から各図式値への Hom の同値だけを要求する。
使われ方：共通 Hom 解像の直値・反転値の全空間比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 局所 Kan な豊穣圏では、元の weighted cone の比較そのものは全空間の前合成同値。 -/
lemma weightedCoherentConeComparison_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentConeComparison F x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isPrecompositionEquivalence_of_leftFibration_fibers
    ((SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentConeComparison F x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentConeComparison_over F x)
  intro b
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentConeFiberMap_homotopyEquivalence F x b).isQCatEquivalence

/-- 元の Hom の点ごとの同値は、反転した weighted 係数図式の全空間の同値を与える。 -/
lemma weightedHomFunctorImage_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C)
    (hR : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (R.map x (F.obj i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence ((SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap
        (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedHomFunctorImage F R x) SSet.opFunctor))) := by
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i => inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
      (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x) ⋙ SSet.opFunctor).obj i) :=
    fun i => inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (R.obj x) (R.obj (F.obj i))).op)
  let η : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x) ⋙
        SSet.opFunctor) := Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedHomFunctorImage F R x) SSet.opFunctor
  have hη := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_isPrecompositionEquivalence η (fun i =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence (hR i).isSimplicialHomotopyEquivalence).isQCatEquivalence)
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection _)
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x) ⋙
        SSet.opFunctor)) := quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection _)
  exact hη.isQCatEquivalence.ulift.isPrecompositionEquivalence

/-- 同じ底上の実際の cone 全空間の後合成は、始点からの Hom が同値なら前合成同値。 -/
lemma coherentConeTotalFunctorImage_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C)
    (hR : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (R.map x (F.obj i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentConeTotalFunctorImage F R x) := by
  apply (weightedCoherentConeComparison_isPrecompositionEquivalence F x).cancel_left
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedCoherentConeComparison_functorImage]
  exact (weightedHomFunctorImage_isPrecompositionEquivalence F R x hR).comp
    (weightedCoherentConeComparison_isPrecompositionEquivalence
      (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
