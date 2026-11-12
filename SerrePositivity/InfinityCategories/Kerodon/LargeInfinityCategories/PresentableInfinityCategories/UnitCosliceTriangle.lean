module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitTransport

/-!
概要：coslice の辺の二単体を、元の圏の単位の可換三角形として読む。
方針：点と辺の join を標準二単体に直し、三つの面を計算する。
規約：単位の代表辺を選び直さない。
使われ方：随伴単位の条件を対応空間の辺に沿って移送する。

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

/-- 概要：coslice の辺は元の二つの単位辺と底の辺の可換三角形を与える。
方針：join の二単体の三面を計算して合成構造を構成する。
規約：この二単体の構成には充填性を要求しない。
使われ方：単位条件の同型不変性に渡す元の三角形。 -/
def cosliceUnitCompStruct {X : SSet.{u}} (x : X _⦋0⦌)
    {s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))) s t) :
    SSet.Truncated.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x s)
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x t) := by
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ e.edge.val
  have hv (i : Fin 2) : stdSimplex.δ i.succ ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ i) ≫ e.edge.val) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one, Category.assoc]
    dsimp [F]
    rw [Iso.hom_inv_id_assoc]
  refine ⟨SSet.yonedaEquiv F, ?_, ?_, ?_⟩
  · change X.δ 2 (SSet.yonedaEquiv F) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x s).edge
    rw [← stdSimplex.yonedaEquiv_δ_comp,
      show (2 : Fin 3) = (1 : Fin 2).succ from rfl, hv]
    have hs := congrArg Subtype.val e.src_eq
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ 1) ≫ e.edge.val = s.val at hs
    rw [hs]
    rfl
  · change X.δ 0 (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inr, Category.assoc]
    dsimp only [F]
    rw [Iso.hom_inv_id_assoc]
    rfl
  · change X.δ 1 (SSet.yonedaEquiv F) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x t).edge
    rw [← stdSimplex.yonedaEquiv_δ_comp,
      show (1 : Fin 3) = (0 : Fin 2).succ from rfl, hv]
    have ht := congrArg Subtype.val e.tgt_eq
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ 0) ≫ e.edge.val = t.val at ht
    rw [ht]
    rfl

/-- 概要：coslice の辺は元のホモトピー圏で指定単位の可換三角形を与える。
方針：同じ二単体の合成構造の h での関係を使う。
規約：元の quasicategory の h 全体での等式。
使われ方：元の単位を保持する随伴移送の公式と照合する。 -/
lemma cosliceUnit_homMk_comp {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
    {s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))) s t) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x s) ≫
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk e) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x t) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (cosliceUnitCompStruct x e)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
