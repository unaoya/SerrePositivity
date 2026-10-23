module

public import SerrePositivity.InfinityCategories.F1.Transport.SquareVertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexFiberTotalIso

/-!
概要：底を固定した全空間の同型は可換四角形の空間の同型を与える。
方針：pointed space 側だけを全空間の射で前合成する。
規約：底の分類図式を厳密に保持する。
使われ方：積の具体的な全空間と底変換の引き戻し全空間を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の全空間の射で四角形を前合成する。
方針：分類図式を保ち pointed space への射を合成する。
規約：全空間の射の同値性を要求しない。
使われ方：全空間の同型による四角形の同型の頂点作用。 -/
def LeftTransportSquare.totalPre {E F B : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ B}
    (S : LeftTransportSquare q) (f : E ⟶ F) (hf : f ≫ q = p) : LeftTransportSquare p :=
  ⟨S.diagram, f ≫ S.pointedMap, by rw [Category.assoc, S.comm, ← Category.assoc, hf]⟩

/-- 概要：底上の全空間の射による四角形空間の前合成。
方針：全空間側の内部 Hom の前合成と不変の分類図式を引き戻しへ束ねる。
規約：全高次単体の射。
使われ方：実際の引き戻しへの比較の周囲の射。 -/
def transportSquareTotalPre {E F B : SSet.{u + 1}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) : transportSquareSpace q ⟶ transportSquareSpace p :=
  pullback.lift (transportSquarePointed q ≫ (pre f).app PointedSpaceInfinity)
    (transportSquareDiagram q) (by
      rw [Category.assoc, pre_comm_ihom_map, ← Category.assoc, transportSquareSpace_condition,
        Category.assoc, ← NatTrans.comp_app, ← pre_map, hf])

/-- 概要：全空間の前合成の pointed space 側の射影は指定した前合成。
方針：引き戻しへの lift の第一射影。
規約：厳密な射の一致。
使われ方：底変換全空間との比較の可換性。 -/
lemma transportSquareTotalPre_pointed {E F B : SSet.{u + 1}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) :
    transportSquareTotalPre p q f hf ≫ transportSquarePointed p =
      transportSquarePointed q ≫ (pre f).app PointedSpaceInfinity := pullback.lift_fst _ _ _

/-- 概要：全空間の前合成は底の分類図式を保つ。
方針：引き戻しへの lift の第二射影。
規約：厳密な射の一致。
使われ方：分類図式を変更せず全空間だけを同定する。 -/
lemma transportSquareTotalPre_diagram {E F B : SSet.{u + 1}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) :
    transportSquareTotalPre p q f hf ≫ transportSquareDiagram p = transportSquareDiagram q :=
  pullback.lift_snd _ _ _

/-- 概要：底上の全空間の同型は四角形空間の厳密な同型を与える。
方針：同型の両方向で前合成し、二つの射影で逆性を確認する。
規約：元の射影の充填性は不要。
使われ方：実際の引き戻し全空間と積全空間の翻訳。 -/
def transportSquareTotalIso {E F B : SSet.{u + 1}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) : transportSquareSpace q ≅ transportSquareSpace p := by
  have hi : e.inv ≫ p = q := by rw [← he, Iso.inv_hom_id_assoc]
  refine { hom := transportSquareTotalPre p q e.hom he
           inv := transportSquareTotalPre q p e.inv hi
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · change (transportSquareTotalPre p q e.hom he ≫ transportSquareTotalPre q p e.inv hi) ≫
        transportSquarePointed q = _
      rw [Category.assoc, transportSquareTotalPre_pointed, ← Category.assoc,
        transportSquareTotalPre_pointed, Category.assoc, ← NatTrans.comp_app, ← pre_map,
        Iso.inv_hom_id, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
      rfl
    · change (transportSquareTotalPre p q e.hom he ≫ transportSquareTotalPre q p e.inv hi) ≫
        transportSquareDiagram q = _
      rw [Category.assoc, transportSquareTotalPre_diagram, transportSquareTotalPre_diagram,
        Category.id_comp]
      rfl
  · apply pullback.hom_ext
    · change (transportSquareTotalPre q p e.inv hi ≫ transportSquareTotalPre p q e.hom he) ≫
        transportSquarePointed p = _
      rw [Category.assoc, transportSquareTotalPre_pointed, ← Category.assoc,
        transportSquareTotalPre_pointed, Category.assoc, ← NatTrans.comp_app, ← pre_map,
        Iso.hom_inv_id, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
      rfl
    · change (transportSquareTotalPre q p e.inv hi ≫ transportSquareTotalPre p q e.hom he) ≫
        transportSquareDiagram p = _
      rw [Category.assoc, transportSquareTotalPre_diagram, transportSquareTotalPre_diagram,
        Category.id_comp]
      rfl

/-- 概要：全空間の前合成は頂点で実際の四角形の前合成を回収する。
方針：二つの射影の関手頂点を比較する。
規約：分類図式と全空間の射を同時に保持する。
使われ方：表現条件の全部分複体への同型の制限。 -/
lemma transportSquareTotalPre_vertex {E F B : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ B}
    (S : LeftTransportSquare q) (f : E ⟶ F) (hf : f ≫ q = p) :
    (transportSquareTotalPre p q f hf).app _ (transportSquareVertex S) =
      transportSquareVertex (S.totalPre f hf) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom E).map pointedSpaceProjection)
      ((pre p).app SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (transportSquareTotalPre p q f hf ≫ transportSquarePointed p).app _
      (transportSquareVertex S) = _
    rw [transportSquareTotalPre_pointed]
    change ((pre f).app PointedSpaceInfinity).app _
      ((transportSquarePointed q).app _ (transportSquareVertex S)) = _
    rw [transportSquareVertex_pointed]
    exact (transportSquareVertex_pointed (S.totalPre f hf)).symm
  · change (transportSquareTotalPre p q f hf ≫ transportSquareDiagram p).app _
      (transportSquareVertex S) = _
    rw [transportSquareTotalPre_diagram, transportSquareVertex_diagram]
    exact (transportSquareVertex_diagram (S.totalPre f hf)).symm

end SerrePositivity.InfinityCategories
