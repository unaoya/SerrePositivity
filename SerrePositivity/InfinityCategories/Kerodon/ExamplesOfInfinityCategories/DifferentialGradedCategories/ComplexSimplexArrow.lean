module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangles
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexEdgeEquivalence

/-! # 複体 dg nerve の一単体と実際の射

概要：任意の一単体を通常の chain map として読み、同じ一単体をその射から復元する。
方針：閉零射の同値と端点付き辺の閉零 cycle の同値を使う。
規約：HA Example 1.3.1.8。使われ方：任意の cospan と四角形から標準 fiber の入力を抽出する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：複体 dg nerve の一単体は二つの端点の間の通常の chain map を定める。
方針：一単体の閉零射を通常の複体の射へ変換する。
規約：HA Example 1.3.1.8。使われ方：cospan の二つの脚の射。 -/
def simplexChainMap (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1) : s.obj 0 ⟶ s.obj 1 :=
  _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv A _ _ (s.edgeClosed 0 1 (by decide))

/-- 概要：一単体から取り出した chain map の cochain は元の辺の成分。
方針：閉零射と cycle の両逆関係を評価する。
規約：HA Example 1.3.1.8。使われ方：元の一単体の復元。 -/
lemma simplexChainMap_cochain (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1) :
    Cochain.ofHom (simplexChainMap s) = s.edgeHom 0 1 (by decide) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap, complexClosedHomEquiv_cochain]
  change (closedHomEquiv A (Complex A) _ _ (s.edgeClosed 0 1 (by decide))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeClosed, Equiv.apply_symm_apply]
  rfl

/-- 概要：一単体をその二つの対象を端点とする辺として読む。
方針：両端の零単体を頂点同値で同定する。
規約：HA Example 1.3.1.8。使われ方：辺と閉零 cycle の同値による復元。 -/
def simplexAsEdge (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1) :
    SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (Complex A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (s.obj 0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (s.obj 1)) where
  edge := s
  src_eq := by apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective; rfl
  tgt_eq := by apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective; rfl

/-- 概要：任意の一単体は取り出した chain map の complexEdge で復元される。
方針：端点付き辺と閉零 cycle の同値で比較し、cochain の評価を使う。
規約：HA Example 1.3.1.8。使われ方：標準 fiber の cospan と元の cospan の厳密な一致。 -/
lemma complexEdge_simplexChainMap (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s)).edge = s := by
  have H : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s)).toTruncated = simplexAsEdge s := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycleEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (s.obj 0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (s.obj 1))).injective
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (simplexChainMap s)).toTruncated).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (simplexAsEdge s)).val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_cycle, simplexChainMap_cochain]
    exact (eq_of_heq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq (simplexAsEdge s))).symm
  exact congrArg (fun e => e.edge) H

/-- 概要：終域の等式による同定を射の後に合成しても、対応する一単体は変わらない。
方針：終域の等式を消去して恒等射との合成へ戻す。
規約：HA Example 1.3.1.8。使われ方：cospan の二つの脚の共通終域を合わせる。 -/
lemma complexEdge_comp_eqToHom {X Y Z : Complex A} (f : X ⟶ Y) (h : Y = Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (f ≫ eqToHom h)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).edge := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
