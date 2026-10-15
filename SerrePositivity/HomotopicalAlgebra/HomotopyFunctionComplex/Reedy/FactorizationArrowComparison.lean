module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeFactorizationStep
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDegree

/-! # Relative arrow comparisons for an actual degree factorization step

The comparisons are isomorphisms of arrows of attaching diagrams. Applying
the relative boundary functors transports the classes of the selected source
factorization through the ordinary closed-degree diagram construction.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.DegreeFactorizationStep
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (hinj : Function.Injective r.deg)
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {F G : J ⥤ C} (τ : F ⟶ G)
  {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
  (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight
    (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ))
  {left right : MorphismProperty C}
  (q : MorphismProperty.MapFactorizationData left right
    (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) a))


abbrev localLeft := BoundaryDiagram.homOfMap
  (RelativeExtension.leftMap (BoundaryExtension.mapOfNatTrans r j τ) a q)

abbrev localRight := BoundaryDiagram.homOfMap
  (RelativeExtension.rightMap (BoundaryExtension.mapOfNatTrans r j τ) a q)

def leftBoundaryIso :
    Arrow.mk ((BoundaryDiagram.fromUpperFunctor r j C).map (leftMap r j hinj τ a q)) ≅
      Arrow.mk (localLeft r j τ a q) := by
  let B := BoundaryDiagram.fromUpperFunctor r j C
  let R := BoundaryDiagram.degreeReconstructionIso r j C hinj
  let D := BoundaryDiagram.ofExtension (BoundaryExtension.ofFunctor r j F)
  let E := BoundaryDiagram.ofExtension
    (RelativeExtension.extension (BoundaryExtension.mapOfNatTrans r j τ) a q)
  let m := localLeft r j τ a q
  let f := BoundaryExtension.degreeOfFunctorIso r j F hinj
  refine Arrow.isoMk (B.mapIso f.symm ≪≫ R.app D) (R.app E) ?_
  have h := R.hom.naturality m
  change B.map ((BoundaryDiagram.degreeFunctor r j C hinj).map m) ≫ (R.app E).hom =
    (R.app D).hom ≫ m at h
  change (B.map f.inv ≫ (R.app D).hom) ≫ m =
    B.map (f.inv ≫ (BoundaryDiagram.degreeFunctor r j C hinj).map m) ≫ (R.app E).hom
  rw [B.map_comp, Category.assoc, ← h, Category.assoc]

def rightBoundaryIso :
    Arrow.mk ((BoundaryDiagram.fromUpperFunctor r j C).map (rightMap r j hinj τ a q)) ≅
      Arrow.mk (localRight r j τ a q) := by
  let B := BoundaryDiagram.fromUpperFunctor r j C
  let R := BoundaryDiagram.degreeReconstructionIso r j C hinj
  let D := BoundaryDiagram.ofExtension
    (RelativeExtension.extension (BoundaryExtension.mapOfNatTrans r j τ) a q)
  let E := BoundaryDiagram.ofExtension (BoundaryExtension.ofFunctor r j G)
  let m := localRight r j τ a q
  let g := BoundaryExtension.degreeOfFunctorIso r j G hinj
  refine Arrow.isoMk (R.app D) (B.mapIso g.symm ≪≫ R.app E) ?_
  have h := R.hom.naturality m
  change B.map ((BoundaryDiagram.degreeFunctor r j C hinj).map m) ≫ (R.app E).hom =
    (R.app D).hom ≫ m at h
  have hc : B.map g.hom ≫ B.map g.inv = 𝟙 _ := by
    rw [← B.map_comp, g.hom_inv_id, B.map_id]
  change (R.app D).hom ≫ m =
    B.map ((BoundaryDiagram.degreeFunctor r j C hinj).map m ≫ g.hom) ≫
      (B.map g.inv ≫ (R.app E).hom)
  rw [B.map_comp, Category.assoc, ← Category.assoc (B.map g.hom), hc, Category.id_comp]
  exact h.symm

lemma leftBoundary_mem [left.RespectsIso] :
    left (((BoundaryDiagram.relativeLatchingArrow r j C).obj
      (Arrow.mk ((BoundaryDiagram.fromUpperFunctor r j C).map
        (leftMap r j hinj τ a q)))).hom) := by
  apply (left.arrow_iso_iff ((BoundaryDiagram.relativeLatchingArrow r j C).mapIso
    (leftBoundaryIso r j hinj τ a q))).mpr
  exact RelativeExtension.relativeLeft_mem (BoundaryExtension.mapOfNatTrans r j τ) a q

lemma rightBoundary_mem [right.RespectsIso] :
    right (((BoundaryDiagram.relativeMatchingArrow r j C).obj
      (Arrow.mk ((BoundaryDiagram.fromUpperFunctor r j C).map
        (rightMap r j hinj τ a q)))).hom) := by
  apply (right.arrow_iso_iff ((BoundaryDiagram.relativeMatchingArrow r j C).mapIso
    (rightBoundaryIso r j hinj τ a q))).mpr
  exact RelativeExtension.relativeRight_mem (BoundaryExtension.mapOfNatTrans r j τ) a q

end SerrePositivity.Reedy.DegreeFactorizationStep
