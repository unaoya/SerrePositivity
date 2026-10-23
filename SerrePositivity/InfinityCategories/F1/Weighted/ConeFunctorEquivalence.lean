module

public import SerrePositivity.InfinityCategories.F1.Weighted.ConeTotalFunctorImage
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanUnstraighteningComparison
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveMapComparison
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeKanHomotopy

/-!
概要：weighted cone の全空間の後合成は、実際の Hom の同値から同値となる。
方針：元の weighted 比較の fiber 判定と、係数図式の同値を可換式で消去する。
規約：始点から各図式値への Hom の同値だけを要求する。
使われ方：共通 Hom 解像の直値・反転値の全空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 局所 Kan な豊穣圏では、元の weighted cone の比較そのものは全空間の前合成同値。 -/
lemma weightedCoherentConeComparison_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    IsPrecompositionEquivalence (weightedCoherentConeComparison F x) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
    (weightedCoherentConeComparison F x) (weightedCoherentConeComparison_over F x)
  intro b
  exact (weightedCoherentConeFiberMap_homotopyEquivalence F x b).isQCatEquivalence

/-- 元の Hom の点ごとの同値は、反転した weighted 係数図式の全空間の同値を与える。 -/
lemma weightedHomFunctorImage_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C)
    (hR : ∀ i, IsQCatEquivalence (R.map x (F.obj i))) :
    IsPrecompositionEquivalence ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveMap
        (Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor))) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i => inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have : ∀ i, KanComplex ((simplicialHomDiagram
      (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x) ⋙ SSet.opFunctor).obj i) :=
    fun i => inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (R.obj x) (R.obj (F.obj i))).op)
  let η : (simplicialHomDiagram F x ⋙ SSet.opFunctor) ⟶
      (simplicialHomDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x) ⋙
        SSet.opFunctor) := Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor
  have hη := weightedNerveMap_isPrecompositionEquivalence η (fun i =>
    (oppositeKanHomotopyEquivalence (hR i).isSimplicialHomotopyEquivalence).isQCatEquivalence)
  have : Quasicategory (weightedNerve (simplicialHomDiagram F x ⋙ SSet.opFunctor)) :=
    quasicategory_of_innerFibration (weightedNerveProjection _)
  have : Quasicategory (weightedNerve
      (simplicialHomDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x) ⋙
        SSet.opFunctor)) := quasicategory_of_innerFibration (weightedNerveProjection _)
  exact hη.isQCatEquivalence.ulift.isPrecompositionEquivalence

/-- 同じ底上の実際の cone 全空間の後合成は、始点からの Hom が同値なら前合成同値。 -/
lemma coherentConeTotalFunctorImage_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C)
    (hR : ∀ i, IsQCatEquivalence (R.map x (F.obj i))) :
    IsPrecompositionEquivalence (coherentConeTotalFunctorImage F R x) := by
  apply (weightedCoherentConeComparison_isPrecompositionEquivalence F x).cancel_left
  rw [weightedCoherentConeComparison_functorImage]
  exact (weightedHomFunctorImage_isPrecompositionEquivalence F R x hR).comp
    (weightedCoherentConeComparison_isPrecompositionEquivalence
      (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x))

end SerrePositivity.InfinityCategories
