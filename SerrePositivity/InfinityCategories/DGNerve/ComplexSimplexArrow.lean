module
public import SerrePositivity.InfinityCategories.DGNerve.ComplexTriangles
public import SerrePositivity.InfinityCategories.DGNerve.ComplexEdgeEquivalence

/-! # 複体 dg nerve の一単体と実際の射

概要：任意の一単体を通常の chain map として読み、同じ一単体をその射から復元する。
方針：閉零射の同値と端点付き辺の閉零 cycle の同値を使う。
規約：HA Example 1.3.1.8。使われ方：任意の cospan と四角形から標準 fiber の入力を抽出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory DifferentialGraded CochainComplex HomComplex HomotopyComparison
open scoped Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：複体 dg nerve の一単体は二つの端点の間の通常の chain map を定める。
方針：一単体の閉零射を通常の複体の射へ変換する。
規約：HA Example 1.3.1.8。使われ方：cospan の二つの脚の射。 -/
def simplexChainMap (s : Simplex A (Complex A) 1) : s.obj 0 ⟶ s.obj 1 :=
  complexClosedHomEquiv A _ _ (s.edgeClosed 0 1 (by decide))

/-- 概要：一単体から取り出した chain map の cochain は元の辺の成分。
方針：閉零射と cycle の両逆関係を評価する。
規約：HA Example 1.3.1.8。使われ方：元の一単体の復元。 -/
lemma simplexChainMap_cochain (s : Simplex A (Complex A) 1) :
    Cochain.ofHom (simplexChainMap s) = s.edgeHom 0 1 (by decide) := by
  rw [simplexChainMap, complexClosedHomEquiv_cochain]
  change (closedHomEquiv A (Complex A) _ _ (s.edgeClosed 0 1 (by decide))).val = _
  rw [Simplex.edgeClosed, Equiv.apply_symm_apply]
  rfl

/-- 概要：一単体をその二つの対象を端点とする辺として読む。
方針：両端の零単体を頂点同値で同定する。
規約：HA Example 1.3.1.8。使われ方：辺と閉零 cycle の同値による復元。 -/
def simplexAsEdge (s : Simplex A (Complex A) 1) :
    SSet.Truncated.Edge (X := twoTruncation A (Complex A))
      (Simplex.vertex (s.obj 0)) (Simplex.vertex (s.obj 1)) where
  edge := s
  src_eq := by apply Simplex.vertexEquiv.injective; rfl
  tgt_eq := by apply Simplex.vertexEquiv.injective; rfl

/-- 概要：任意の一単体は取り出した chain map の complexEdge で復元される。
方針：端点付き辺と閉零 cycle の同値で比較し、cochain の評価を使う。
規約：HA Example 1.3.1.8。使われ方：標準 fiber の cospan と元の cospan の厳密な一致。 -/
lemma complexEdge_simplexChainMap (s : Simplex A (Complex A) 1) :
    (complexEdge (simplexChainMap s)).edge = s := by
  have H : (complexEdge (simplexChainMap s)).toTruncated = simplexAsEdge s := by
    apply (edgeCycleEquiv (Simplex.vertex (s.obj 0)) (Simplex.vertex (s.obj 1))).injective
    apply Subtype.ext
    change (edgeCycle (complexEdge (simplexChainMap s)).toTruncated).val =
      (edgeCycle (simplexAsEdge s)).val
    rw [complexEdge_cycle, simplexChainMap_cochain]
    exact (eq_of_heq (edgeCycle_val_heq (simplexAsEdge s))).symm
  exact congrArg (fun e => e.edge) H

/-- 概要：終域の等式による同定を射の後に合成しても、対応する一単体は変わらない。
方針：終域の等式を消去して恒等射との合成へ戻す。
規約：HA Example 1.3.1.8。使われ方：cospan の二つの脚の共通終域を合わせる。 -/
lemma complexEdge_comp_eqToHom {X Y Z : Complex A} (f : X ⟶ Y) (h : Y = Z) :
    (complexEdge (f ≫ eqToHom h)).edge = (complexEdge f).edge := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.DGNerve
