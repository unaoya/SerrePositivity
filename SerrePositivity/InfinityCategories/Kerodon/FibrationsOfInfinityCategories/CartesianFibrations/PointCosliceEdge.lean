module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-!
概要：点の coslice の頂点と始点を指定した辺の対応。
方針：二つの零単体の join と標準区間の同型を使う。
規約：点を任意の Δ[0] からの射で指定する。
使われ方：Kerodon §5.1.1（Tag 01T4） の cocartesian な coslice。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：点の coslice の頂点はその点から始まる辺を与える。
方針：点と点の join を標準辺に直して両端を計算する。
規約：点 a は Δ[0] からの任意の射。
使われ方：Kerodon §5.1.1（Tag 01T4） の coslice の対象としての辺。 -/
def pointCosliceVertexEdge {E : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌) :
    Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) σ) where
  edge := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ σ.val)
  src_eq := by
    change E.δ 1 (SSet.yonedaEquiv _) = SSet.yonedaEquiv a
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, Category.assoc, Iso.hom_inv_id_assoc, σ.property]
  tgt_eq := by
    change E.δ 0 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id_assoc]
    rfl

/-- 概要：点の coslice の辺の表示は標的への射に自然。
方針：Yoneda の後合成の自然性を使う。
規約：比較するのは辺の一次単体。
使われ方：Kerodon §5.1.1（Tag 01T4） の基底上の辺の表示。 -/
lemma pointCosliceVertexEdge_postcomp {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌) :
    (pointCosliceVertexEdge (a ≫ p) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) σ)).edge =
      p.app (Opposite.op ⦋1⦌) (pointCosliceVertexEdge a σ).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ (σ.val ≫ p)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

/-- 概要：始点を指定した辺を点の coslice の頂点へ戻す。
方針：標準辺からの射を二点の join に戻し、始点条件を固定図式の条件にする。
規約：a は Δ[0] からの射、辺の始点はその Yoneda 頂点。
使われ方：Kerodon §5.1.1（Tag 01T4） の cocartesian な辺の持ち上げ。 -/
def pointCosliceVertexOfEdge {E : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    {y : E _⦋0⦌} (e : Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, stdSimplex.δ_comp_yonedaEquiv_symm]
    have hs : E.δ 1 e.edge = SSet.yonedaEquiv a := e.src_eq
    rw [hs, Equiv.symm_apply_apply]⟩

/-- 概要：点の coslice へ戻した辺の一次単体は元の辺。
方針：標準辺との同型と Yoneda 同値の逆則を使う。
規約：両端の等式の証明の選択は問わない。
使われ方：Kerodon §5.1.1（Tag 01T4） の cocartesian な対象の表示。 -/
lemma pointCosliceVertexEdge_ofEdge {E : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    {y : E _⦋0⦌} (e : Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y) :
    (pointCosliceVertexEdge a (pointCosliceVertexOfEdge a e)).edge = e.edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
