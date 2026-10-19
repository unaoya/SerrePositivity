module

public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：始域と底の同型で可換な四角形は頂点の fiber の同型を誘導する。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {E E' B B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
  (a : E ≅ E') (b : B ≅ B') (w : p ≫ b.hom = a.hom ≫ q) (x : B _⦋0⦌)

/-- 概要：可換な同型の四角形から fiber の順方向の射を作る。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanVertexFiberSquareHom : vertexFiber p x ⟶ vertexFiber q (b.hom.app _ x) :=
  vertexFiberLift q (b.hom.app _ x) (vertexFiberι p x ≫ a.hom) (by
    rw [Category.assoc, ← w, ← Category.assoc, vertexFiberι_comp, SSet.const_comp])

/-- 概要：逆同型による射を元の頂点の fiber へ持ち上げる。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanVertexFiberSquareInv : vertexFiber q (b.hom.app _ x) ⟶ vertexFiber p x :=
  vertexFiberLift p x (vertexFiberι q (b.hom.app _ x) ≫ a.inv) (by
    apply (cancel_mono b.hom).1
    have hi : a.inv ≫ p ≫ b.hom = q := by
      rw [w, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [Category.assoc, Category.assoc, hi, vertexFiberι_comp, SSet.const_comp])

/-- 概要：可換な同型の四角形は fiber の同型を誘導する。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanVertexFiberSquareIso : vertexFiber p x ≅ vertexFiber q (b.hom.app _ x) where
  hom := kanVertexFiberSquareHom p q a b w x
  inv := kanVertexFiberSquareInv p q a b w x
  hom_inv_id := by
    apply vertexFiber_hom_ext p x
    change kanVertexFiberSquareHom p q a b w x ≫ kanVertexFiberSquareInv p q a b w x ≫
      vertexFiberι p x = 𝟙 _ ≫ vertexFiberι p x
    dsimp only [kanVertexFiberSquareHom, kanVertexFiberSquareInv]
    rw [vertexFiberLift_ι, ← Category.assoc, vertexFiberLift_ι,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply vertexFiber_hom_ext q (b.hom.app _ x)
    dsimp only [kanVertexFiberSquareHom, kanVertexFiberSquareInv]
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, vertexFiberLift_ι,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 概要：fiber の同型は全空間の同型と可換。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma kanVertexFiberSquareIso_hom_inclusion : (kanVertexFiberSquareIso p q a b w x).hom ≫
    vertexFiberι q (b.hom.app _ x) = vertexFiberι p x ≫ a.hom := rfl

/-- 概要：頂点の等式による fiber の輸送は全空間への包含を保つ。
方針：頂点の等式で置換して恒等同型に帰着する。
規約：射 p は固定する。
使われ方：指数比較で写した関手頂点の正規化。 -/
lemma kanVertexFiberι_eqTransport {X Y : SSet.{u}} (f : X ⟶ Y)
    {v v' : Y _⦋0⦌} (hv : v = v') :
    (eqToIso (congrArg (vertexFiber f) hv)).hom ≫ vertexFiberι f v' = vertexFiberι f v := by
  cases hv
  simp

end SerrePositivity.InfinityCategories.F1B
