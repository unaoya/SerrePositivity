module
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import SerrePositivity.KST.SConstruction.PointedSSetObject

/-! # 元の点つき span 図式全体の標準 end 豊穣
概要：同じ三つの値と二つの矢を持つ span の全自然変換を、標準の end Hom で豊穣化する。
方針：小さい WalkingSpan と単体集合の極限を使い、標準点つき豊穣を図式全体へ移す。
規約：写像空間を成分の頂点だけに弱めない。使われ方：関手的 BF の span 入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 元の同じ三つの点つき値と二つの前向き矢を持つ、実際の span 図式。 -/
structure PointedSpanDiagram where
  diagram : WalkingSpan ⥤ PointedSSetObject.{u}

/-- 通常射は、元の同じ span 図式間の自然変換。 -/
instance pointedSpanDiagram_category : Category.{u} PointedSpanDiagram.{u} where
  Hom X Y := X.diagram ⟶ Y.diagram
  id X := 𝟙 X.diagram
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 三つの全 basedHom を二つの矢に自然に揃える、標準 end の単体的豊穣。 -/
instance pointedSpanDiagram_simplicialCategory : SimplicialCategory PointedSpanDiagram.{u} where
  Hom X Y := Enriched.FunctorCategory.enrichedHom SSet X.diagram Y.diagram
  id X := Enriched.FunctorCategory.enrichedId SSet X.diagram
  comp X Y Z := Enriched.FunctorCategory.enrichedComp SSet X.diagram Y.diagram Z.diagram
  id_comp X Y := Enriched.FunctorCategory.enriched_id_comp SSet X.diagram Y.diagram
  comp_id X Y := Enriched.FunctorCategory.enriched_comp_id SSet X.diagram Y.diagram
  assoc W X Y Z := Enriched.FunctorCategory.enriched_assoc SSet
    W.diagram X.diagram Y.diagram Z.diagram
  homEquiv := Enriched.FunctorCategory.homEquiv SSet
  homEquiv_id X := Enriched.FunctorCategory.homEquiv_id SSet X.diagram
  homEquiv_comp f g := Enriched.FunctorCategory.homEquiv_comp SSet f g

/-- 標準 end の全族から、同じ元の一頂点の全 basedHom への実射影。 -/
def pointedSpanProjection (X Y : PointedSpanDiagram.{u}) (i : WalkingSpan) :
    (X ⟶[SSet.{u}] Y) ⟶ (X.diagram.obj i ⟶[SSet.{u}] Y.diagram.obj i) :=
  Enriched.FunctorCategory.enrichedHomπ SSet X.diagram Y.diagram i

/-- 元の三頂点への全族射影は、二つの元の矢の前後合成に厳密に自然。 -/
lemma pointedSpanProjection_naturality (X Y : PointedSpanDiagram.{u})
    {i j : WalkingSpan} (f : i ⟶ j) :
    pointedSpanProjection X Y i ≫ eHomWhiskerLeft SSet (X.diagram.obj i) (Y.diagram.map f) =
      pointedSpanProjection X Y j ≫ eHomWhiskerRight SSet (X.diagram.map f) (Y.diagram.obj j) :=
  Enriched.FunctorCategory.enrichedHom_condition SSet X.diagram Y.diagram f

end SerrePositivity.KST.SConstruction
