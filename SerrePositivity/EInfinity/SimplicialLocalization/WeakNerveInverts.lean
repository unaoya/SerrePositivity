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

lemma weakNerveEdges_inverts_of_arrows (C : RelativeCategory.{u}) {E : SSet.{u}}
    (F : nerve C.category ⟶ E)
    (h : ∀ {X Y : C.category} (f : X ⟶ Y), C.weakEquivalences f →
      IsInvertibleEdge ((nerve.edgeMk f).map F).toTruncated) :
    InvertsEdges F (weakNerveEdges C) := by
  intro s hs
  obtain ⟨X, Y, f, hf, rfl⟩ := hs
  exact (isInvertibleEdge_congr (e := ((nerve.edgeMk f).map F).toTruncated)
    (f := (edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F)) rfl).mp
      (h f hf)

end SerrePositivity.EInfinity.SimplicialLocalization
