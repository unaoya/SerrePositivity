module
public import SerrePositivity.KST.SConstruction.PointedSpanEnrichment
public import SerrePositivity.KST.SConstruction.PointedPushoutFamily
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker

/-! # 元の標準 end span の同じ点つき押し出しと両包含
概要：実 span の三頂点と二矢を保った、点つき圏の同じ押し出しを選ぶ。
方針：通常射を元の点つき圏へ戻し、実 pushout を標準豊穣の対象として包装する。
規約：同値な別対象への置換はしない。使われ方：押し出しの全 Hom 作用。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 元の span の左向きの実脚。 -/
def pointedSpanPushoutLeftMap (X : PointedSpanDiagram.{u}) :
    (X.diagram.obj .zero).obj ⟶ (X.diagram.obj .left).obj :=
  X.diagram.map WalkingSpan.Hom.fst

/-- 元の span の右向きの実脚。 -/
def pointedSpanPushoutRightMap (X : PointedSpanDiagram.{u}) :
    (X.diagram.obj .zero).obj ⟶ (X.diagram.obj .right).obj :=
  X.diagram.map WalkingSpan.Hom.snd

/-- 元の二脚の、点つき圏における実押し出し。 -/
def pointedSpanPushout (X : PointedSpanDiagram.{u}) : PointedSSetObject.{u} :=
  ⟨pushout (pointedSpanPushoutLeftMap X) (pointedSpanPushoutRightMap X)⟩

/-- 同じ実押し出しの元の左包含。 -/
def pointedSpanPushoutInl (X : PointedSpanDiagram.{u}) :
    X.diagram.obj .left ⟶ pointedSpanPushout X :=
  show (X.diagram.obj .left).obj ⟶ (pointedSpanPushout X).obj from
    pushout.inl (pointedSpanPushoutLeftMap X) (pointedSpanPushoutRightMap X)

/-- 同じ実押し出しの元の右包含。 -/
def pointedSpanPushoutInr (X : PointedSpanDiagram.{u}) :
    X.diagram.obj .right ⟶ pointedSpanPushout X :=
  show (X.diagram.obj .right).obj ⟶ (pointedSpanPushout X).obj from
    pushout.inr (pointedSpanPushoutLeftMap X) (pointedSpanPushoutRightMap X)

/-- 同じ実押し出しの両包含は、元の二脚で厳密に一致する。 -/
lemma pointedSpanPushout_condition (X : PointedSpanDiagram.{u}) :
    X.diagram.map WalkingSpan.Hom.fst ≫ pointedSpanPushoutInl X =
      X.diagram.map WalkingSpan.Hom.snd ≫ pointedSpanPushoutInr X :=
  pushout.condition (f := pointedSpanPushoutLeftMap X) (g := pointedSpanPushoutRightMap X)

end SerrePositivity.KST.SConstruction
