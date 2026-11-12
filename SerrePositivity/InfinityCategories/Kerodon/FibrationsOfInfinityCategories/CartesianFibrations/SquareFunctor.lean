module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareVertices
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：可換四角形空間を射の圏上の反変関手にする。
方針：可換正方形の底側と全空間側で同時に前合成する。
規約：充填性や fiber の同値性を仮定しない。
使われ方：底の貼り合わせを四角形空間の極限へ移す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：射の圏の可換正方形で実際の四角形を前合成する。
方針：底と全空間の二射をそれぞれ合成する。
規約：正方形の pullback 性を要求しない。
使われ方：四角形空間の反変作用の頂点表示。 -/
def LeftTransportSquare.preSquare {p q : Arrow SSet.{u + 1}}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare q.hom) (f : p ⟶ q) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p.hom :=
  ⟨f.right ≫ S.diagram, f.left ≫ S.pointedMap, by
    rw [Category.assoc, S.comm, ← Category.assoc, f.w, Category.assoc]⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (preSquare)


/-- 概要：可換正方形による四角形空間の前合成。
方針：内部 Hom の二つの前合成を引き戻しへ束ねる。
規約：全高次単体の射として構成する。
使われ方：余極限上の四角形を各項へ制限する。 -/
def transportSquarePre {p q : Arrow SSet.{u + 1}} (f : p ⟶ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace q.hom ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p.hom :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed q.hom ≫ (pre f.left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q.hom ≫ (pre f.right).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) (by
      rw [Category.assoc, pre_comm_ihom_map, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition, Category.assoc, Category.assoc]
      congr 1
      rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map, f.w])

/-- 概要：可換正方形の前合成の全空間側の射影は指定した前合成。
方針：引き戻しへの lift の第一射影。
規約：厳密な射の等式。
使われ方：貼り合わせで全空間側の図式を回収する。 -/
lemma transportSquarePre_pointed {p q : Arrow SSet.{u + 1}} (f : p ⟶ q) :
    transportSquarePre f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed q.hom ≫ (pre f.left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity :=
  pullback.lift_fst _ _ _

/-- 概要：可換正方形の前合成の底側の射影は指定した前合成。
方針：引き戻しへの lift の第二射影。
規約：厳密な射の等式。
使われ方：貼り合わせで分類図式を回収する。 -/
lemma transportSquarePre_diagram {p q : Arrow SSet.{u + 1}} (f : p ⟶ q) :
    transportSquarePre f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q.hom ≫ (pre f.right).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity :=
  pullback.lift_snd _ _ _

/-- 概要：恒等正方形の前合成は四角形空間の恒等射。
方針：二射影で内部 Hom の恒等前合成を計算する。
規約：全高次単体の厳密な一致。
使われ方：反変関手の恒等射則。 -/
lemma transportSquarePre_id (p : Arrow SSet.{u + 1}) : transportSquarePre (𝟙 p) = 𝟙 _ := by
  apply pullback.hom_ext
  · change transportSquarePre (𝟙 p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom = _
    rw [transportSquarePre_pointed]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom ≫ (pre (𝟙 p.left)).app _ = _
    rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
    rfl
  · change transportSquarePre (𝟙 p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom = _
    rw [transportSquarePre_diagram]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom ≫ (pre (𝟙 p.right)).app _ = _
    rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
    rfl

/-- 概要：可換正方形の合成は四角形空間の前合成を反変に合成する。
方針：両射影で前合成の合成則を使う。
規約：全高次単体の厳密な一致。
使われ方：反変関手の合成則。 -/
lemma transportSquarePre_comp {p q r : Arrow SSet.{u + 1}} (f : p ⟶ q) (g : q ⟶ r) :
    transportSquarePre (f ≫ g) = transportSquarePre g ≫ transportSquarePre f := by
  apply pullback.hom_ext
  · change transportSquarePre (f ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom =
      (transportSquarePre g ≫ transportSquarePre f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom
    rw [transportSquarePre_pointed, Category.assoc, transportSquarePre_pointed,
      ← Category.assoc, transportSquarePre_pointed, Category.assoc]
    change _ ≫ (pre (f.left ≫ g.left)).app _ = _
    rw [pre_map, NatTrans.comp_app]
  · change transportSquarePre (f ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom =
      (transportSquarePre g ≫ transportSquarePre f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom
    rw [transportSquarePre_diagram, Category.assoc, transportSquarePre_diagram,
      ← Category.assoc, transportSquarePre_diagram, Category.assoc]
    change _ ≫ (pre (f.right ≫ g.right)).app _ = _
    rw [pre_map, NatTrans.comp_app]

/-- 概要：可換四角形の空間は射の圏上の反変関手。
方針：可換正方形の前合成を恒等射則と合成則で束ねる。
規約：定義は left fibration に限らない。
使われ方：底の余極限に沿う表現の降下の周囲の関手。 -/
def transportSquareFunctor : (Arrow SSet.{u + 1})ᵒᵖ ⥤ SSet.{u + 1} where
  obj p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p.unop.hom
  map f := transportSquarePre f.unop
  map_id p := transportSquarePre_id p.unop
  map_comp f g := transportSquarePre_comp g.unop f.unop

/-- 概要：可換正方形の前合成は頂点で実際の四角形の前合成を回収する。
方針：二射影の関手頂点を比較する。
規約：底側と全空間側の両方を保持する。
使われ方：表現条件の全部分複体への前合成の制限。 -/
lemma transportSquarePre_vertex {p q : Arrow SSet.{u + 1}}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare q.hom) (f : p ⟶ q) :
    (transportSquarePre f).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (S.preSquare f) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom p.left).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
      ((pre p.hom).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (transportSquarePre f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [transportSquarePre_pointed]
    change ((pre f.left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed q.hom).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed (S.preSquare f)).symm
  · change (transportSquarePre f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [transportSquarePre_diagram]
    change ((pre f.right).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q.hom).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram (S.preSquare f)).symm

/-- 概要：四角形の全空間側への射影は射の圏上で自然。
方針：可換正方形の前合成の第一射影公式。
規約：全高次単体の自然変換。
使われ方：余極限の内部 Hom の極限に四角形の錐を写す。 -/
def transportSquareFunctorPointed : transportSquareFunctor.{u} ⟶
    Arrow.leftFunc.op ⋙ (internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity where
  app p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.unop.hom
  naturality _ _ f := transportSquarePre_pointed f.unop

/-- 概要：四角形の分類図式への射影は射の圏上で自然。
方針：可換正方形の前合成の第二射影公式。
規約：全高次単体の自然変換。
使われ方：底の分類図式の貼り合わせ。 -/
def transportSquareFunctorDiagram : transportSquareFunctor.{u} ⟶
    Arrow.rightFunc.op ⋙ (internalHom (C := SSet.{u + 1})).flip.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity where
  app p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.unop.hom
  naturality _ _ f := transportSquarePre_diagram f.unop

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
