module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-! # 極限錐と反転した余極限余錐

概要：錐の反転は極限性を余極限性へ移し、両者は同値となる。
方針：slice の反転と coslice の同型、始対象と終対象の反転を組み合わせる。
規約：値域に quasicategory 性を仮定しない。
使われ方：S4 の引き戻し四角形の貼り合わせへの双対化。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：同型による頂点の像は始対象性を保つ。
方針：反転した終対象性を同型で移し、元の始対象性へ戻す。
規約：値域に追加の仮定なし。使われ方：反転した錐の普遍性。 -/
lemma IsInitialVertex.map_of_isIso {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q]
    {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (q.app (Opposite.op ⦋0⦌) x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_of_isTerminalVertex_op
  exact hx.op_isTerminalVertex.map_of_isIso (SSet.opFunctor.map q)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsInitialVertex (map_of_isIso)


/-- 概要：同型は頂点の始対象性を保存し反映する。
方針：順方向と逆方向の同型で移し、合成を恒等に戻す。
規約：任意の単体集合の同型。使われ方：slice の反転の比較。 -/
lemma isInitialVertex_iff_of_isIso {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (q.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · exact IsInitialVertex.map_of_isIso q
  · intro h
    have ht := h.map_of_isIso (inv q)
    rw [← NatTrans.comp_app_apply, IsIso.hom_inv_id] at ht
    exact ht

/-- 概要：頂点が終対象であることは反転した頂点が始対象であることと同値。
方針：終対象の反転と、二重反転の同型による帰還を使う。
規約：値域の追加の仮定なし。使われ方：極限から余極限への双対化。 -/
lemma isTerminalVertex_iff_isInitialVertex_op {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := X.op) (SSet.opObjEquiv.symm x) := by
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsTerminalVertex.op_isInitialVertex
  · intro h
    have ht := h.op_isTerminalVertex.map_of_isIso (SSet.opFunctorCompOpFunctorIso.app X).hom
    exact ht

/-- 概要：図式 p の錐を反転した図式への余錐にする。
方針：slice の反転の同型を零単体に適用する。
規約：反転後の基底は K.op。使われ方：引き戻し四角形の押し出しへの移し替え。 -/
def JoinCone.reverseCocone {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.opFunctor.map p) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).hom.app (Opposite.op ⦋0⦌)
    (SSet.opObjEquiv.symm (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋0⦌ from c))

/-- 概要：錐が極限であることは反転した余錐が余極限であることと同値。
方針：終対象性を反転で始対象性へ移し、slice／coslice の同型を適用する。
規約：図式も値域も任意。使われ方：S4 の貼り合わせの双対化。 -/
lemma isLimitCone_iff_reverseCocone {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c.reverseCocone := by
  exact (isTerminalVertex_iff_isInitialVertex_op (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋0⦌ from c)).trans
    (isInitialVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).hom _)

/-- 概要：反転した余錐の頂点は元の錐の頂点の反転である。
方針：slice の反転同型と頂点射影の可換性を零次数で使う。
規約：opObjEquiv による移送で書く。使われ方：極限対象と余極限対象の双対比較。 -/
lemma JoinCone.reverseCocone_vertex {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (K := K.op) (X := X.op) (p := SSet.opFunctor.map p) c.reverseCocone =
      (SSet.opObjEquiv (X := X) (n := Opposite.op ⦋0⦌)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (p := p) c) := by
  unfold JoinCone.reverseCocone _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex
  let x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op _⦋0⦌ :=
    SSet.opObjEquiv.symm (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋0⦌ from c)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.opFunctor.map p)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).hom.app (Opposite.op ⦋0⦌) x) =
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).app (Opposite.op ⦋0⦌) x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso_projection p) (Opposite.op ⦋0⦌)) x
  simpa only [NatTrans.comp_app_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
