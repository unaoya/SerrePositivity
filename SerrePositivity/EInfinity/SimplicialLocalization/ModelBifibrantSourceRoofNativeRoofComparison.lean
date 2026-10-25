module

public import SerrePositivity.EInfinity.Hammock.LeftRoofSameUniverseComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofCornerEvaluation

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Limits Opposite SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaDiagram_map_weak
    {s t : modelBifibrantSourceRoofProductComma X Y q b} (f : s ⟶ t) :
    (modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantSourceRoofProductCommaDiagram X Y q b).map f) :=
  modelBifibrantDKFrame_map_weak X q ((modelBifibrantSourceFrameElementDegree X Y q).map f.left)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap :
    nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    Hammock.graph (modelBifibrantRelativeCategory C).weakEquivalences Hammock.LeftRoof.word
      (modelBifibrantObject C X)
      (modelBifibrantObject C Y) :=
  Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap _
    (Hammock.LeftRoof.diagram _ (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (modelBifibrantSourceRoofProductCommaAugmentation X Y q b)
      (modelBifibrantSourceRoofProductCommaAugmentation_weak X Y q b)
      (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
      (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaAugmentationRoofMap :
    nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    Hammock.colimitGraph (modelBifibrantRelativeCategory C).weakEquivalences
      (modelBifibrantObject C X)
      (modelBifibrantObject C Y) :=
  Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap _
    (Hammock.LeftRoof.diagram _ (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (modelBifibrantSourceRoofProductCommaAugmentation X Y q b)
      (modelBifibrantSourceRoofProductCommaAugmentation_weak X Y q b)
      (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
      (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaEvaluationRoofMap :
    nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    Hammock.colimitGraph (modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantDKFrame X q).obj (modelBifibrantSourceRoofDegree X Y q b))
      (modelBifibrantObject C Y) :=
  Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap _
    (Hammock.LeftRoof.diagram _ (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
      (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
      (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
      (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaEvaluationRoofMap_sourceComparison :
    AnodyneHomotopy.anodyneQ.map (modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b) =
      AnodyneHomotopy.anodyneQ.map (modelBifibrantSourceRoofProductCommaAugmentationRoofMap X
        Y q b) ≫
        AnodyneHomotopy.anodyneQ.map (Hammock.precomposePointMap
          (Hammock.arrowMap (modelBifibrantRelativeCategory C).weakEquivalences
            ((modelBifibrantDKFrameAugmentation X q).app (modelBifibrantSourceRoofDegree X Y q b)))
          (modelBifibrantObject C Y)) := by
  have h : (𝟙 (modelBifibrantSourceRoofProductCommaDiagram X Y q b)) ≫
      modelBifibrantSourceRoofProductCommaAugmentation X Y q b =
    modelBifibrantSourceRoofProductCommaEvaluation X Y q b ≫
      (Functor.const (modelBifibrantSourceRoofProductComma X Y q b)).map
        ((modelBifibrantDKFrameAugmentation X q).app (modelBifibrantSourceRoofDegree X Y q b)) := by
    rw [Category.id_comp]
    exact (modelBifibrantSourceRoofProductCommaAugmentation_triangle X Y q b).symm
  simpa only [Category.id_comp, modelBifibrantSourceRoofProductCommaEvaluationRoofMap,
    modelBifibrantSourceRoofProductCommaAugmentationRoofMap] using
    Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_sourceComparison
      (modelBifibrantRelativeCategory C).weakEquivalences
      (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
      (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
      (modelBifibrantSourceRoofProductCommaAugmentation X Y q b)
      (modelBifibrantSourceRoofProductCommaAugmentation_weak X Y q b)
      (𝟙 _) ((modelBifibrantDKFrameAugmentation X q).app (modelBifibrantSourceRoofDegree X Y q b))
      (modelBifibrantSourceRoofProductCommaRightLeg X Y q b) h
      (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f)
      (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f)

end SerrePositivity.EInfinity.SimplicialLocalization
