module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentationRestriction

/-!
概要：可換四角形の空間に対する底変換の制限作用。
方針：二つの関手空間で前合成し、底変換の引き戻し条件でまとめる。
規約：制限は全次数の射であり、頂点では両方の実際の射を保つ。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、表現空間の制限写像の周囲の作用。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance transportSquarePullbackLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：可換四角形のデータを任意の底変換に制限する。
方針：底側は g、全空間側は引き戻しの第一射影で前合成する。
規約：表現の fiber 同値条件を仮定しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、周囲の四角形の頂点での制限。 -/
noncomputable def LeftTransportSquare.restrict {E B D : SSet.{u + 1}}
    {p : E ⟶ B} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (pullback.snd p g) :=
  ⟨g ≫ S.diagram, pullback.fst p g ≫ S.pointedMap, by
    rw [Category.assoc, S.comm, ← Category.assoc, pullback.condition, Category.assoc]⟩

/-- 概要：表現の制限から四角形を取り出す操作は四角形の制限と一致する。
方針：表現の制限が底側と全空間側の両射を厳密に保つことを使う。
規約：四角形そのものの等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現条件が制限で保たれることの検査。 -/
lemma LeftTransportRepresentation.restrict_toSquare {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (g : D ⟶ B) :
    (R.restrict g).toSquare = R.toSquare.restrict g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.ext
  · rfl
  · exact R.restrict_pointedMap g

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (restrict_toSquare)


/-- 概要：可換四角形の空間の底変換による制限。
方針：両側の関手空間の前合成の自然性と底変換の四角形を使う。
規約：高次のパラメーターを保持する。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、制限写像の全次数での定義。 -/
noncomputable def transportSquareRestriction {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (pullback.snd p g) :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p ≫ (pre (pullback.fst p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p ≫ (pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) (by
      rw [Category.assoc, pre_comm_ihom_map, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition, Category.assoc, Category.assoc]
      congr 1
      rw [← NatTrans.comp_app, ← pre_map, pullback.condition, pre_map, NatTrans.comp_app])

/-- 概要：四角形の制限の底側は元の分類図式の前合成。
方針：引き戻しへの持ち上げの第二射影を計算する。
規約：全パラメーターの厳密な等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、境界で固定する分類図式の比較。 -/
lemma transportSquareRestriction_diagram {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) :
    transportSquareRestriction p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.snd p g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p ≫ (pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := pullback.lift_snd _ _ _

/-- 概要：四角形の制限の全空間側は元の pointed space 値図式の前合成。
方針：引き戻しへの持ち上げの第一射影を計算する。
規約：全パラメーターの厳密な等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、境界で固定する全空間の射の比較。 -/
lemma transportSquareRestriction_pointed {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) :
    transportSquareRestriction p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.snd p g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p ≫ (pre (pullback.fst p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity :=
  pullback.lift_fst _ _ _

/-- 概要：四角形の空間の制限は頂点で厳密な四角形の制限を回収する。
方針：両射影の計算と関手頂点の前合成の公式を使う。
規約：底側と全空間側の両方で指定の射を保持する。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現の部分空間への制限の持ち上げ。 -/
lemma transportSquareRestriction_vertex {E B D : SSet.{u + 1}}
    {p : E ⟶ B} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (g : D ⟶ B) :
    (transportSquareRestriction p g).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (S.restrict g) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom (pullback p g)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
      ((pre (pullback.snd p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (transportSquareRestriction p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.snd p g)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [transportSquareRestriction_pointed]
    change ((pre (pullback.fst p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.snd p g)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (S.restrict g))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed]
    rfl
  · change (transportSquareRestriction p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.snd p g)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [transportSquareRestriction_diagram]
    change ((pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.snd p g)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (S.restrict g))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
