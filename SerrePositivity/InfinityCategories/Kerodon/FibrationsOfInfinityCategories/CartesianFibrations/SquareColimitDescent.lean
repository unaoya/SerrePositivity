module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareColimitLift
public import Mathlib.CategoryTheory.Limits.Comma

/-!
概要：四角形空間の反変関手は底と全空間の余極限を極限へ移す。
方針：貼り合わせの存在と二つの内部 Hom の極限による一意性を合わせる。
規約：全高次の図式と全空間の射を厳密に回収する。
使われ方：底のセル貼り合わせと骨格列に沿う表現の降下。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：貼り合わせた四角形の全空間側の射を回収する。
方針：引き戻しへの lift の第一射影。
規約：パラメーターを保持する。
使われ方：降下の普遍射の制限公式。 -/
lemma transportSquareColimitLift_pointed {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed c.pt.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitPointedLift c hcE s := pullback.lift_fst _ _ _

/-- 概要：貼り合わせた四角形の分類図式を回収する。
方針：引き戻しへの lift の第二射影。
規約：パラメーターを保持する。
使われ方：降下の普遍射の制限公式。 -/
lemma transportSquareColimitLift_diagram {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram c.pt.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitDiagramLift c hcB s := pullback.lift_snd _ _ _

/-- 概要：貼り合わせた四角形は各項の指定された四角形を厳密に回収する。
方針：二射影で内部 Hom の極限の脚公式を使う。
規約：全高次単体での射の一致。
使われ方：降下の極限錐の脚公式。 -/
lemma transportSquareColimitLift_fac {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre (c.ι.app j) =
      s.π.app (Opposite.op j) := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (D.obj j).hom =
      s.π.app (Opposite.op j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (D.obj j).hom
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_pointed, ← Category.assoc,
      transportSquareColimitLift_pointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitPointedLift_fac]
  · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (D.obj j).hom =
      s.π.app (Opposite.op j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (D.obj j).hom
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_diagram, ← Category.assoc,
      transportSquareColimitLift_diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitDiagramLift_fac]

/-- 概要：余極限上の四角形は全ての各項への制限で一意に決まる。
方針：二つの内部 Hom の極限の脚で比較し、四角形の二射影を同定する。
規約：全高次パラメーターの射についての一意性。
使われ方：降下の極限の普遍性。 -/
lemma transportSquareColimitLift_unique {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c))
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) (m : s.pt ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace c.pt.hom)
    (hm : ∀ j, m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre (c.ι.app j) = s.π.app (Opposite.op j)) :
    m = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s := by
  apply pullback.hom_ext
  · change m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed c.pt.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed c.pt.hom
    rw [transportSquareColimitLift_pointed]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePointedCone_isLimit c hcE).hom_ext
    intro j
    change (m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed c.pt.hom) ≫
        (pre (c.ι.app j.unop).left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitPointedLift c hcE s ≫
        (pre (c.ι.app j.unop).left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitPointedLift_fac]
    have h := congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (D.obj j.unop).hom) (hm j.unop)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_pointed] at h
    simpa only [Category.assoc] using h
  · change m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram c.pt.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram c.pt.hom
    rw [transportSquareColimitLift_diagram]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareDiagramCone_isLimit c hcB).hom_ext
    intro j
    change (m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram c.pt.hom) ≫
        (pre (c.ι.app j.unop).right).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitDiagramLift c hcB s ≫
        (pre (c.ι.app j.unop).right).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitDiagramLift_fac]
    have h := congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (D.obj j.unop).hom) (hm j.unop)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_diagram] at h
    simpa only [Category.assoc] using h

/-- 概要：底と全空間が余極限を成すとき四角形空間の制限錐は極限。
方針：二つの図式の貼り合わせと一意性を極限の普遍性に束ねる。
規約：fibration 性と単射性は不要。
使われ方：表現空間の底の貼り合わせの周囲の降下定理。 -/
def transportSquareColimitCone_isLimit {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hcE : IsColimit (Arrow.leftFunc.mapCocone c))
    (hcB : IsColimit (Arrow.rightFunc.mapCocone c)) : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitCone c) where
  lift s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitLift c hcE hcB s
  fac s j := transportSquareColimitLift_fac c hcE hcB s j.unop
  uniq s m hm := transportSquareColimitLift_unique c hcE hcB s m (fun j ↦ hm (Opposite.op j))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
