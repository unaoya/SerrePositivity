module
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutHom
public import SerrePositivity.KST.SConstruction.PointedSpanEvaluationFunctor
public import SerrePositivity.KST.SConstruction.SimplicialCoconeLaws

/-! # 元の標準 end span から同じ実押し出しへの厳密豊穣関手
概要：全 span 自然変換の実押し出し作用が、同じ恒等・合成を厳密に保つことを証明する。
方針：元の両包含に制限し、各頂点の豊穣関手性と余錐の自然性で検出する。
規約：通常射の圏だけへ制限しない。使われ方：実写像円柱と homotopy pushout。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 同じ実押し出しの全 Hom 作用は、元の豊穣恒等射を保つ。 -/
lemma pointedSpanPushoutHom_id (X : PointedSpanDiagram.{u}) :
    eId SSet X ≫ pointedSpanPushoutHom X X = eId SSet (pointedSpanPushout X) := by
  apply pointedSpanPushoutHom_ext X (pointedSpanPushout X)
  · exact simplicialCocone_map_id (pointedSpanEvaluationFunctor .left) X
      (pointedSpanPushout X) (pointedSpanPushoutHom X X) (pointedSpanPushoutInl X)
      (pointedSpanPushoutHom_inl X X)
  · exact simplicialCocone_map_id (pointedSpanEvaluationFunctor .right) X
      (pointedSpanPushout X) (pointedSpanPushoutHom X X) (pointedSpanPushoutInr X)
      (pointedSpanPushoutHom_inr X X)

/-- 同じ実押し出しの全 Hom 作用は、元の豊穣合成を厳密に保つ。 -/
lemma pointedSpanPushoutHom_comp (X Y Z : PointedSpanDiagram.{u}) :
    eComp SSet X Y Z ≫ pointedSpanPushoutHom X Z =
      (pointedSpanPushoutHom X Y ⊗ₘ pointedSpanPushoutHom Y Z) ≫
        eComp SSet (pointedSpanPushout X) (pointedSpanPushout Y) (pointedSpanPushout Z) := by
  apply pointedSpanPushoutHom_ext X (pointedSpanPushout Z)
  · rw [Category.assoc, pointedSpanPushoutHom_inl X Z]
    change eComp SSet X Y Z ≫
        (pointedSpanProjection X Z .left ≫
          eHomWhiskerLeft SSet (X.diagram.obj .left) (pointedSpanPushoutInl Z)) = _
    rw [← Category.assoc]
    exact (simplicialCocone_map_comp (pointedSpanEvaluationFunctor .left) X Y Z
      (pointedSpanPushout X) (pointedSpanPushout Y) (pointedSpanPushout Z)
      (pointedSpanPushoutInl X) (pointedSpanPushoutInl Y) (pointedSpanPushoutInl Z)
      (pointedSpanPushoutHom X Y) (pointedSpanPushoutHom Y Z)
      (pointedSpanPushoutHom_inl X Y) (pointedSpanPushoutHom_inl Y Z)).symm
  · rw [Category.assoc, pointedSpanPushoutHom_inr X Z]
    change eComp SSet X Y Z ≫
        (pointedSpanProjection X Z .right ≫
          eHomWhiskerLeft SSet (X.diagram.obj .right) (pointedSpanPushoutInr Z)) = _
    rw [← Category.assoc]
    exact (simplicialCocone_map_comp (pointedSpanEvaluationFunctor .right) X Y Z
      (pointedSpanPushout X) (pointedSpanPushout Y) (pointedSpanPushout Z)
      (pointedSpanPushoutInr X) (pointedSpanPushoutInr Y) (pointedSpanPushoutInr Z)
      (pointedSpanPushoutHom X Y) (pointedSpanPushoutHom Y Z)
      (pointedSpanPushoutHom_inr X Y) (pointedSpanPushoutHom_inr Y Z)).symm

/-- 元の標準 end の全 span から、同じ実押し出しへの厳密単体的豊穣関手。 -/
def pointedSpanPushoutEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSpanDiagram.{u} PointedSSetObject.{u} where
  obj := pointedSpanPushout
  map := pointedSpanPushoutHom
  map_id := pointedSpanPushoutHom_id
  map_comp := pointedSpanPushoutHom_comp

end SerrePositivity.KST.SConstruction
