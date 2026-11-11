module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareFunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：射の図式の余極限から四角形空間の錐と二つの内部 Hom の極限を作る。
方針：反変関手の作用で錐を取り、反変内部 Hom の極限保存を使う。
規約：通常の単体集合の余極限の普遍性のみを用いる。
使われ方：全高次パラメーターで四角形を貼り合わせる。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：射の図式上の余錐の各項へ四角形を制限する錐。
方針：四角形の反変関手で反対の錐を写す。
規約：余錐の余極限性は定義に不要。
使われ方：四角形空間の降下の極限錐。 -/
def transportSquareColimitCone {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D) :
    Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor.mapCone c.op

/-- 概要：四角形空間の錐から全空間側の内部 Hom の錐を取る。
方針：自然な第一射影で各脚を後合成する。
規約：錐のパラメーターを保持する。
使われ方：全空間側の図式を余極限へ貼り合わせる。 -/
def transportSquareConePointed {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    Cone ((D ⋙ Arrow.leftFunc).op ⋙
      (internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity) :=
  (Cone.postcompose (Functor.whiskerLeft D.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctorPointed)).obj s

/-- 概要：四角形空間の錐から底側の内部 Hom の錐を取る。
方針：自然な第二射影で各脚を後合成する。
規約：錐のパラメーターを保持する。
使われ方：分類図式を底の余極限へ貼り合わせる。 -/
def transportSquareConeDiagram {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor)) :
    Cone ((D ⋙ Arrow.rightFunc).op ⋙
      (internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) :=
  (Cone.postcompose (Functor.whiskerLeft D.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctorDiagram)).obj s

/-- 概要：全空間の余極限の内部 Hom の錐は極限。
方針：反変内部 Hom の極限保存を使う。
規約：全空間の Kan 性は要求しない。
使われ方：全空間側の貼り合わせの存在と一意性。 -/
def transportSquarePointedCone_isLimit {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hc : IsColimit (Arrow.leftFunc.mapCocone c)) :
    IsLimit (((internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).mapCone
      (Arrow.leftFunc.mapCocone c).op) :=
  isLimitOfPreserves _ hc.op

/-- 概要：底の余極限の内部 Hom の錐は極限。
方針：反変内部 Hom の極限保存を使う。
規約：底の quasicategory 性は要求しない。
使われ方：分類図式の貼り合わせの存在と一意性。 -/
def transportSquareDiagramCone_isLimit {J : Type v} [Category.{w} J]
    {D : J ⥤ Arrow SSet.{u + 1}} (c : Cocone D)
    (hc : IsColimit (Arrow.rightFunc.mapCocone c)) :
    IsLimit (((internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).mapCone
      (Arrow.rightFunc.mapCocone c).op) :=
  isLimitOfPreserves _ hc.op

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
