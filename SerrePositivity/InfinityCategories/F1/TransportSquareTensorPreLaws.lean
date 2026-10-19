module

public import SerrePositivity.InfinityCategories.F1.TransportSquareTensorPre

/-!
概要：積上の四角形のパラメーター制限の自然性と頂点公式。
方針：両射影で内部 currying の自然性を確認する。
規約：任意のパラメーターの射で厳密に可換する。
使われ方：表現空間の境界制限と内部 Hom の境界制限を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：積上の四角形のパラメーター制限は内部 Hom の前合成と可換。
方針：引き戻しの二射影で内部 currying の自然性を使う。
規約：頂点だけでなく全高次単体の厳密な等式。
使われ方：区間族と境界族の比較の周囲の正方形。 -/
lemma transportSquareTensorIso_hom_naturality {E B : SSet.{u + 1}}
    (p : E ⟶ B) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportSquareTensorPre p i ≫ (transportSquareTensorIso p L).hom =
      (transportSquareTensorIso p K).hom ≫ (pre i).app (transportSquareSpace p) := by
  apply ((IsPullback.of_hasPullback ((ihom E).map pointedSpaceProjection)
    ((pre p).app SpaceInfinity)).map (ihom L)).hom_ext
  · change (transportSquareTensorPre p i ≫ (transportSquareTensorIso p L).hom) ≫
      (ihom L).map (transportSquarePointed p) = _
    rw [Category.assoc, transportSquareTensorIso_hom_pointed,
      ← Category.assoc, transportSquareTensorPre_pointed]
    simp only [Category.assoc]
    rw [transportIhomCurry_pre_whiskerLeft, pre_comm_ihom_map, ← Category.assoc]
    have h := congrArg (fun f ↦ f ≫ (pre i).app ((ihom E).obj PointedSpaceInfinity))
      (transportSquareTensorIso_hom_pointed p K).symm
    simpa only [Category.assoc, transportSquarePointed, transportSquareDiagram] using h
  · change (transportSquareTensorPre p i ≫ (transportSquareTensorIso p L).hom) ≫
      (ihom L).map (transportSquareDiagram p) = _
    rw [Category.assoc, transportSquareTensorIso_hom_diagram,
      ← Category.assoc, transportSquareTensorPre_diagram]
    simp only [Category.assoc]
    rw [transportIhomCurry_pre_whiskerLeft, pre_comm_ihom_map, ← Category.assoc]
    have h := congrArg (fun f ↦ f ≫ (pre i).app ((ihom B).obj SpaceInfinity))
      (transportSquareTensorIso_hom_diagram p K).symm
    simpa only [Category.assoc, transportSquarePointed, transportSquareDiagram] using h

/-- 概要：四角形空間のパラメーター制限は頂点で実際の四角形の前合成を回収する。
方針：引き戻しの二射影の頂点を計算する。
規約：分類図式と全空間の射をともに保つ。
使われ方：全部分複体へ制限を持ち上げるときの頂点条件。 -/
lemma transportSquareTensorPre_vertex {E B K L : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare (p ▷ K)) (i : L ⟶ K) :
    (transportSquareTensorPre p i).app _ (transportSquareVertex S) =
      transportSquareVertex (S.tensorPre i) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom (E ⊗ L)).map pointedSpaceProjection)
      ((pre (p ▷ L)).app SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (transportSquareTensorPre p i ≫ transportSquarePointed (p ▷ L)).app _
      (transportSquareVertex S) = _
    rw [transportSquareTensorPre_pointed]
    change ((pre (E ◁ i)).app PointedSpaceInfinity).app _
      ((transportSquarePointed (p ▷ K)).app _ (transportSquareVertex S)) = _
    rw [transportSquareVertex_pointed]
    exact (transportSquareVertex_pointed (S.tensorPre i)).symm
  · change (transportSquareTensorPre p i ≫ transportSquareDiagram (p ▷ L)).app _
      (transportSquareVertex S) = _
    rw [transportSquareTensorPre_diagram]
    change ((pre (B ◁ i)).app SpaceInfinity).app _
      ((transportSquareDiagram (p ▷ K)).app _ (transportSquareVertex S)) = _
    rw [transportSquareVertex_diagram]
    exact (transportSquareVertex_diagram (S.tensorPre i)).symm

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
    (S : LeftTransportSquare (p ▷ K)) (i : L ⟶ K) (l : L _⦋0⦌) :
    (S.tensorPre i).tensorAt l = S.tensorAt (i.app _ l) := by
  apply LeftTransportSquare.ext
  · change lift (𝟙 B) (SSet.const l) ≫ ((B ◁ i) ≫ S.diagram) = _
    rw [← Category.assoc, transportTensorVertexSection_naturality]
    rfl
  · change lift (𝟙 E) (SSet.const l) ≫ ((E ◁ i) ≫ S.pointedMap) = _
    rw [← Category.assoc, transportTensorVertexSection_naturality]
    rfl

end SerrePositivity.InfinityCategories
