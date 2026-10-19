module

public import SerrePositivity.InfinityCategories.F1.TransportSquareColimitLift
public import Mathlib.CategoryTheory.Limits.Comma

/-!
概要：四角形空間の反変関手は底と全空間の余極限を極限へ移す。
方針：貼り合わせの存在と二つの内部 Hom の極限による一意性を合わせる。
規約：全高次の図式と全空間の射を厳密に回収する。
使われ方：底のセル貼り合わせと骨格列に沿う表現の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：貼り合わせた四角形の全空間側の射を回収する。
方針：引き戻しへの lift の第一射影。
規約：パラメーターを保持する。
使われ方：降下の普遍射の制限公式。 -/
lemma transportSquareColimitLift_pointed {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ transportSquareFunctor)) :
    transportSquareColimitLift c hcE hcB s ≫ transportSquarePointed c.pt.hom =
      transportSquareColimitPointedLift c hcE s := pullback.lift_fst _ _ _

/-- 概要：貼り合わせた四角形の分類図式を回収する。
方針：引き戻しへの lift の第二射影。
規約：パラメーターを保持する。
使われ方：降下の普遍射の制限公式。 -/
lemma transportSquareColimitLift_diagram {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ transportSquareFunctor)) :
    transportSquareColimitLift c hcE hcB s ≫ transportSquareDiagram c.pt.hom =
      transportSquareColimitDiagramLift c hcB s := pullback.lift_snd _ _ _

/-- 概要：貼り合わせた四角形は各項の指定された四角形を厳密に回収する。
方針：二射影で内部 Hom の極限の脚公式を使う。
規約：全高次単体での射の一致。
使われ方：降下の極限錐の脚公式。 -/
lemma transportSquareColimitLift_fac {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ transportSquareFunctor)) (j : J) :
    transportSquareColimitLift c hcE hcB s ≫ transportSquarePre (c.ι.app j) =
      s.π.app (Opposite.op j) := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ transportSquarePointed (D.obj j).hom =
      s.π.app (Opposite.op j) ≫ transportSquarePointed (D.obj j).hom
    rw [Category.assoc, transportSquarePre_pointed, ← Category.assoc,
      transportSquareColimitLift_pointed, transportSquareColimitPointedLift_fac]
  · change (_ ≫ _) ≫ transportSquareDiagram (D.obj j).hom =
      s.π.app (Opposite.op j) ≫ transportSquareDiagram (D.obj j).hom
    rw [Category.assoc, transportSquarePre_diagram, ← Category.assoc,
      transportSquareColimitLift_diagram, transportSquareColimitDiagramLift_fac]

/-- 概要：余極限上の四角形は全ての各項への制限で一意に決まる。
方針：二つの内部 Hom の極限の脚で比較し、四角形の二射影を同定する。
規約：全高次パラメーターの射についての一意性。
使われ方：降下の極限の普遍性。 -/
lemma transportSquareColimitLift_unique {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ transportSquareFunctor)) (m : s.pt ⟶ transportSquareSpace c.pt.hom)
    (hm : ∀ j, m ≫ transportSquarePre (c.ι.app j) = s.π.app (Opposite.op j)) :
    m = transportSquareColimitLift c hcE hcB s := by
  apply pullback.hom_ext
  · change m ≫ transportSquarePointed c.pt.hom =
      transportSquareColimitLift c hcE hcB s ≫ transportSquarePointed c.pt.hom
    rw [transportSquareColimitLift_pointed]
    apply (transportSquarePointedCone_isLimit c hcE).hom_ext
    intro j
    change (m ≫ transportSquarePointed c.pt.hom) ≫
        (pre (c.ι.app j.unop).left).app PointedSpaceInfinity =
      transportSquareColimitPointedLift c hcE s ≫
        (pre (c.ι.app j.unop).left).app PointedSpaceInfinity
    rw [transportSquareColimitPointedLift_fac]
    have h := congrArg (fun f ↦ f ≫ transportSquarePointed (D.obj j.unop).hom) (hm j.unop)
    rw [Category.assoc, transportSquarePre_pointed] at h
    simpa only [Category.assoc] using h
  · change m ≫ transportSquareDiagram c.pt.hom =
      transportSquareColimitLift c hcE hcB s ≫ transportSquareDiagram c.pt.hom
    rw [transportSquareColimitLift_diagram]
    apply (transportSquareDiagramCone_isLimit c hcB).hom_ext
    intro j
    change (m ≫ transportSquareDiagram c.pt.hom) ≫
        (pre (c.ι.app j.unop).right).app SpaceInfinity =
      transportSquareColimitDiagramLift c hcB s ≫
        (pre (c.ι.app j.unop).right).app SpaceInfinity
    rw [transportSquareColimitDiagramLift_fac]
    have h := congrArg (fun f ↦ f ≫ transportSquareDiagram (D.obj j.unop).hom) (hm j.unop)
    rw [Category.assoc, transportSquarePre_diagram] at h
    simpa only [Category.assoc] using h

/-- 概要：底と全空間が余極限を成すとき四角形空間の制限錐は極限。
方針：二つの図式の貼り合わせと一意性を極限の普遍性に束ねる。
規約：fibration 性と単射性は不要。
使われ方：表現空間の底の貼り合わせの周囲の降下定理。 -/
def transportSquareColimitCone_isLimit {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c)) : IsLimit (transportSquareColimitCone c) where
  lift s := transportSquareColimitLift c hcE hcB s
  fac s j := transportSquareColimitLift_fac c hcE hcB s j.unop
  uniq s m hm := transportSquareColimitLift_unique c hcE hcB s m (fun j ↦ hm (Opposite.op j))

end SerrePositivity.InfinityCategories
