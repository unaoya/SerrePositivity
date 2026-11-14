module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberPushoutComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian

/-! # 実 Verdier 分母の基底変更

概要：安定閉包に cofiber を持つ実辺の条件は押し出し・引き戻しで保ち反映される。
方針：同じ実 cofiber 頂点を持つ左右の辺の選択と、cofiber の選択独立性を使う。
規約：指定した実普遍四角形に適用。使われ方：coherent 分数表示の共通分母。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

omit [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] in
/-- 端点つきの任意の辺でも、辺の所属は任意の実 cofiber により判定できる。 -/
lemma cofiberStableEdges_edge_mem_iff (P : Set (X _⦋0⦌))
    {x y : X _⦋0⦌} {f : Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) :
    f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P s.cofiber := by
  let t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex f.edge) := {
    toZeroTriangle := s.toZeroTriangle
    bottom_edge := s.bottom_edge
    isPushout := s.isPushout }
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_mem_iff P t

/-- 実押し出しの左右の辺は、安定閉包の cofiber 分母として同時に所属する。 -/
theorem cofiberStableEdges_pushout_iff (P : Set (X _⦋0⦌))
    (L : Δ[1] ⊗ Δ[1] ⟶ X) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenPushoutCofiberRectangle L hL
  rw [cofiberStableEdges_edge_mem_iff P r.leftCofiberSquare,
    cofiberStableEdges_edge_mem_iff P r.rightCofiberSquare, r.cofiber_eq]

/-- 実引き戻しの左右の辺は、安定閉包の cofiber 分母として同時に所属する。 -/
theorem cofiberStableEdges_pullback_iff (P : Set (X _⦋0⦌))
    (L : Δ[1] ⊗ Δ[1] ⟶ X) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} :=
  cofiberStableEdges_pushout_iff P L (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square L hL)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
