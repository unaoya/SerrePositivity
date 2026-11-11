module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeCoconeEdgeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSimplexEdgeEndpoint

/-!
概要：指定された基底の全単体を保ち、有限全単体へ指定辺を付け加える。
方針：右端の join 表示で相対余錐の辺の持ち上げを適用する。
規約：基底への射影・前段階・最後の辺を全射の等式で保持する。
使われ方：可算辺列の相対実現、望遠鏡形状への制限の充填性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：最後の辺の終点から任意の全単体の最終頂点を回収できる。
方針：最後の辺への制限と零単体への制限を合成する。
規約：指定辺の代表を変更しない。
使われ方：相対的に選んだ全単体の次の延長の始点。 -/
lemma simplexTerminalCocone_vertex_of_lastEdge {X : SSet.{u}} (n : ℕ)
    (f : (Δ[n + 2] : SSet.{u}) ⟶ X) {x y : X _⦋0⦌} (e : X.Edge x y)
    (he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫ f =
      SSet.yonedaEquiv.symm e.edge) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone (n + 1) f).vertex = y := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.joinStdSimplexIso_rightEdge_lastVertex,
    Category.assoc, he, e.δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply]

/-- 概要：元の全単体と指定辺を、指定された基底の全単体へ持ち上げられる。
方針：相対 join 延長を標準単体の join 同型で戻す。
規約：元の射は inner fibration、指定辺の射影も厳密に固定する。
使われ方：指定された可算辺列を基底の全図式上で実現する。 -/
lemma exists_relativeSimplex_edge_extension {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (n : ℕ) (f : (Δ[n + 1] : SSet.{u}) ⟶ X) {y : X _⦋0⦌}
    (e : X.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n f).vertex y)
    (H : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hfront : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ H = f ≫ p)
    (hright : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫ H =
      SSet.yonedaEquiv.symm e.edge ≫ p) :
    ∃ g : (Δ[n + 2] : SSet.{u}) ⟶ X,
      SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ g = f ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫ g =
        SSet.yonedaEquiv.symm e.edge ∧ g ≫ p = H := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n f
  let B := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom ≫ H
  have hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[n]) (SSet.stdSimplex.δ (1 : Fin 2)) ≫ B = c.val ≫ p := by
    dsimp only [B]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.joinStdSimplexIso_rightEdge_zero, Category.assoc, hfront]
    rfl
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[1] ≫ B =
      (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ f) ≫ p := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[n]) (SSet.stdSimplex.δ (1 : Fin 2)) ≫ B) := by
        symm
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
      _ = _ := by rw [hzero, ← Category.assoc, c.property]
  have ht : SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge =
      SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection _ := by
    calc
      _ = SSet.yonedaEquiv.symm c.vertex := e.δ_one_yonedaEquiv_symm
      _ = _ := by
        change SSet.yonedaEquiv.symm
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ f)).app
              (Opposite.op ⦋0⦌) c) = _
        exact (SSet.yonedaEquiv_symm_comp c
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ f))).symm
  obtain ⟨G, _, hG₀, hGe, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_relativeJoin_edge_extension p c
    (SSet.yonedaEquiv.symm e.edge) B ht hfixed hzero (by
      simpa only [B, Category.assoc] using hright)
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).inv ≫ G, ?_, ?_, ?_⟩
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom).mp
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.joinStdSimplexIso_rightEdge_zero, Category.assoc,
      Iso.hom_inv_id_assoc, hG₀]
    rfl
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hGe
  · rw [Category.assoc, hGp]
    dsimp only [B]
    rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
