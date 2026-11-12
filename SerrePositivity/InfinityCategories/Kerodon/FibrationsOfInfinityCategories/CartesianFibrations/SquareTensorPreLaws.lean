module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareTensorPre

/-!
概要：積上の四角形のパラメーター制限の自然性と頂点公式。
方針：両射影で内部 currying の自然性を確認する。
規約：任意のパラメーターの射で厳密に可換する。
使われ方：表現空間の境界制限と内部 Hom の境界制限を比較する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：積上の四角形のパラメーター制限は内部 Hom の前合成と可換。
方針：引き戻しの二射影で内部 currying の自然性を使う。
規約：頂点だけでなく全高次単体の厳密な等式。
使われ方：区間族と境界族の比較の周囲の正方形。 -/
lemma transportSquareTensorIso_hom_naturality {E B : SSet.{u + 1}}
    (p : E ⟶ B) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre p i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p L).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p K).hom ≫ (pre i).app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) := by
  apply ((IsPullback.of_hasPullback ((ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
    ((pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).map (ihom L)).hom_ext
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre p i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p L).hom) ≫
      (ihom L).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p) = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso_hom_pointed,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre_pointed]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportIhomCurry_pre_whiskerLeft, pre_comm_ihom_map, ← Category.assoc]
    have h := congrArg (fun f ↦ f ≫ (pre i).app ((ihom E).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso_hom_pointed p K).symm
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram] using h
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre p i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p L).hom) ≫
      (ihom L).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p) = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso_hom_diagram,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre_diagram]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportIhomCurry_pre_whiskerLeft, pre_comm_ihom_map, ← Category.assoc]
    have h := congrArg (fun f ↦ f ≫ (pre i).app ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso_hom_diagram p K).symm
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram] using h

/-- 概要：四角形空間のパラメーター制限は頂点で実際の四角形の前合成を回収する。
方針：引き戻しの二射影の頂点を計算する。
規約：分類図式と全空間の射をともに保つ。
使われ方：全部分複体へ制限を持ち上げるときの頂点条件。 -/
lemma transportSquareTensorPre_vertex {E B K L : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (p ▷ K)) (i : L ⟶ K) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre p i).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (S.tensorPre i) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom (E ⊗ L)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
      ((pre (p ▷ L)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ L)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre_pointed]
    change ((pre (E ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ K)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed (S.tensorPre i)).symm
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ L)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre_diagram]
    change ((pre (B ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ K)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram (S.tensorPre i)).symm

/-- 概要：固定頂点の挿入はパラメーターの射に自然。
方針：直積の第一成分と定値射の自然性を計算する。
規約：任意の単体集合と頂点。
使われ方：表現条件の前合成による保存。 -/
lemma transportTensorVertexSection_naturality (A : SSet.{u}) {K L : SSet.{u}}
    (i : L ⟶ K) (l : L _⦋0⦌) :
    lift (𝟙 A) (SSet.const l) ≫ (A ◁ i) = lift (𝟙 A) (SSet.const (i.app _ l)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, lift_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd, lift_snd, SSet.const_comp]

/-- 概要：パラメーター制限後の頂点評価は像の頂点での元の評価。
方針：底と全空間に対し固定頂点の挿入の自然性を使う。
規約：四角形そのものの厳密な一致。
使われ方：積上の表現条件を各パラメーターで保つ。 -/
lemma LeftTransportSquare.tensorPre_tensorAt {E B K L : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (p ▷ K)) (i : L ⟶ K) (l : L _⦋0⦌) :
    (S.tensorPre i).tensorAt l = S.tensorAt (i.app _ l) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.ext
  · change lift (𝟙 B) (SSet.const l) ≫ ((B ◁ i) ≫ S.diagram) = _
    rw [← Category.assoc, transportTensorVertexSection_naturality]
    rfl
  · change lift (𝟙 E) (SSet.const l) ≫ ((E ◁ i) ≫ S.pointedMap) = _
    rw [← Category.assoc, transportTensorVertexSection_naturality]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (tensorPre_tensorAt)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
