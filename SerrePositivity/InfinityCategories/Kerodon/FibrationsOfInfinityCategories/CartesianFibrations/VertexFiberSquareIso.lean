module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：始域と底の同型で可換な四角形は頂点の fiber の同型を誘導する。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

variable {E E' B B' : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B')
  (a : E ≅ E') (b : B ≅ B') (w : p ≫ b.hom = a.hom ≫ q) (x : B _⦋0⦌)

/-- 概要：可換な同型の四角形から fiber の順方向の射を作る。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def vertexFiberSquareHom : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (b.hom.app _ x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q (b.hom.app _ x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x ≫ a.hom) (by
    rw [Category.assoc, ← w, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])

/-- 概要：逆同型による射を元の頂点の fiber へ持ち上げる。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def vertexFiberSquareInv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (b.hom.app _ x) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p x (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (b.hom.app _ x) ≫ a.inv) (by
    apply (cancel_mono b.hom).1
    have hi : a.inv ≫ p ≫ b.hom = q := by
      rw [w, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [Category.assoc, Category.assoc, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])

/-- 概要：可換な同型の四角形は fiber の同型を誘導する。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def vertexFiberSquareIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (b.hom.app _ x) where
  hom := vertexFiberSquareHom p q a b w x
  inv := vertexFiberSquareInv p q a b w x
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p x
    change vertexFiberSquareHom p q a b w x ≫ vertexFiberSquareInv p q a b w x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x
    dsimp only [vertexFiberSquareHom, vertexFiberSquareInv]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q (b.hom.app _ x)
    dsimp only [vertexFiberSquareHom, vertexFiberSquareInv]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 概要：fiber の同型は全空間の同型と可換。
方針：fiber の持ち上げと両同型の逆性を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma vertexFiberSquareIso_hom_inclusion : (vertexFiberSquareIso p q a b w x).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (b.hom.app _ x) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x ≫ a.hom := rfl

/-- 概要：頂点の等式による fiber の輸送は全空間への包含を保つ。
方針：頂点の等式で置換して恒等同型に帰着する。
規約：射 p は固定する。
使われ方：指数比較で写した関手頂点の正規化。 -/
lemma vertexFiberι_eqTransport {X Y : SSet.{u}} (f : X ⟶ Y)
    {v v' : Y _⦋0⦌} (hv : v = v') :
    (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber f) hv)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι f v' = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι f v := by
  cases hv
  simp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
