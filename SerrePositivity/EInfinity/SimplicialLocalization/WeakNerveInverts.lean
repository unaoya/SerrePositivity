module

public import SerrePositivity.EInfinity.SimplicialLocalization.HammockInvertsEdges

/-!
# 元の弱同値射の反転から全指定辺の反転へ

概要：通常の各指定射の反転を元の全弱同値辺集合の反転として束ねる。
方針：同じ通常の辺の二つの表示をそのまま同定する。
規約：元の相対圏と全辺を変更しない。
使われ方：具体的な大きい忘却源への計算上限内の代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

lemma weakNerveEdges_inverts_of_arrows (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {E : SSet.{u}}
    (F : nerve C.category ⟶ E)
    (h : ∀ {X Y : C.category} (f : X ⟶ Y), C.weakEquivalences f →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map F).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges C) := by
  intro s hs
  obtain ⟨X, Y, f, hf, rfl⟩ := hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ((nerve.edgeMk f).map F).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F)) rfl).mp
      (h f hf)

/-- 概要：全指定辺の反転は元の各弱同値射の辺を反転する。
方針：元の同じ通常辺の二表示を同定する。
規約：相対圏と実際の射を保持。使われ方：全列の augmentation の反転。 -/
lemma weakNerveEdges_inverts_arrows (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {E : SSet.{u}}
    (F : nerve C.category ⟶ E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges C))
    {X Y : C.category} (f : X ⟶ Y) (hf : C.weakEquivalences f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map F).toTruncated := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ((nerve.edgeMk f).map F).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F)) rfl).mpr
    (h ⟨_, _, f, hf, rfl⟩)

end SerrePositivity.EInfinity.SimplicialLocalization
