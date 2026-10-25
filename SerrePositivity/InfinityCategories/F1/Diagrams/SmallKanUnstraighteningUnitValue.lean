module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictKanUnstraighteningFiberRecovery
public import SerrePositivity.InfinityCategories.F1.Diagrams.KanWeightedUnitFiberRestriction

/-!
概要：指定した小さい unstraightening の値同値による共通解像上の回収。
方針：大きい実比較の因子分解を、fiber 縮小の厳密な可換式で元の宇宙へ戻す。
規約：既存の smallLeftUnstraighteningFiberValueEquivalence 自体を使用する。
使われ方：Ind-S (5) の全 fiber 単位回収と指定点照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- Kan 値を持つ全関手同型を、同じ二射の元の宇宙へ戻す。 -/
def FunctorIso.downOfKan {X Y : SSet.{u}} [KanComplex Y] {f g : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g)) : FunctorIso f g :=
  functorIsoOfSimplicialHomotopy (unliftSimplicialHomotopy e.simplicialHomotopy)

/-- 指定した小さい fiber 値同値の順方向は、元の大きい値比較を厳密に回収する。 -/
lemma smallLeftUnstraighteningFiberValueEquivalence_hom_lift {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningFiberValueEquivalence F b).hom =
      (smallLeftUnstraighteningFiberIso F b).hom ≫
        (leftUnstraighteningFiberValueEquivalence F (ULift.up b)).hom := by
  change (SSet.uliftFunctor.{u + 1, u}).map (uliftMorphismDown _) = _
  exact uliftMorphismDown_lift _

/-- 直値の実比較は共通解像全体で、既存の大きい fiber 値回収を通して右射影へ戻る。 -/
def reversedWeightedKanUnstraighteningComparison_valueCommonIso
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (c : I) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (F.obj c).obj) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c) ≫
        (uliftVertexFiberIso _ (nerveVertex c)).hom ≫
        vertexFiberMap _ _ (reversedWeightedKanUnstraighteningComparison F)
          (reversedWeightedKanUnstraighteningComparison_projection F) (ULift.up (nerveVertex c)) ≫
        (leftUnstraighteningFiberValueEquivalence
          (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (F.obj c).obj)) := by
  rw [kanDiagramUnstraighteningFiberValue_normalization]
  simp only [Category.assoc]
  rw [reassoc_of% (reversedWeightedKanUnstraighteningComparison_fiber_normalization F c)]
  rw [← Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (F.obj c).obj))
    ((SSet.uliftFunctor.{u + 1, u}).map ((directPointHomDiagramIso F).inv.app c)),
    ← Functor.map_comp]
  exact coherentPointedFiberValueCommonIso (F.obj c)

/-- 同じ小さい比較は、指定値回収を通して共通解像の右射影へ戻る。 -/
def smallReversedWeightedKanUnstraighteningComparison_valueCommonIso
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (c : I) :
    FunctorIso
      (edgewiseLeft (F.obj c).obj ≫
        weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c ≫
        vertexFiberMap _ _ (smallReversedWeightedKanUnstraighteningComparison F)
          (smallReversedWeightedKanUnstraighteningComparison_projection F) (nerveVertex c) ≫
        (smallLeftUnstraighteningFiberValueEquivalence
          (kanDiagramCoherentNerve F) (nerveVertex c)).hom)
      (edgewiseRight (F.obj c).obj) := by
  have e := reversedWeightedKanUnstraighteningComparison_valueCommonIso F c
  have he : (SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseLeft (F.obj c).obj ≫
        weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c ≫
        vertexFiberMap _ _ (smallReversedWeightedKanUnstraighteningComparison F)
          (smallReversedWeightedKanUnstraighteningComparison_projection F) (nerveVertex c) ≫
        (smallLeftUnstraighteningFiberValueEquivalence
          (kanDiagramCoherentNerve F) (nerveVertex c)).hom) =
      (SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (F.obj c).obj) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c) ≫
        (uliftVertexFiberIso _ (nerveVertex c)).hom ≫
        vertexFiberMap _ _ (reversedWeightedKanUnstraighteningComparison F)
          (reversedWeightedKanUnstraighteningComparison_projection F) (ULift.up (nerveVertex c)) ≫
        (leftUnstraighteningFiberValueEquivalence
          (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom := by
    simp only [Functor.map_comp, smallLeftUnstraighteningFiberValueEquivalence_hom_lift,
      Category.assoc]
    rw [← Category.assoc
      ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap _ _
        (smallReversedWeightedKanUnstraighteningComparison F)
        (smallReversedWeightedKanUnstraighteningComparison_projection F) (nerveVertex c)))
      (smallLeftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (nerveVertex c)).hom]
    erw [smallLeftUnstraighteningLift_fiber_naturality (kanDiagramCoherentNerve F)
      (weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget))
      (reversedWeightedKanUnstraighteningComparison F)
      (reversedWeightedKanUnstraighteningComparison_projection F) (nerveVertex c)]
    simp only [Category.assoc]
  rw [← he] at e
  exact FunctorIso.downOfKan e

end SerrePositivity.InfinityCategories
