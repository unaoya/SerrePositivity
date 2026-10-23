module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackTerminalVertices
public import SerrePositivity.InfinityCategories.Core.InnerPullback
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-!
概要：任意の厳密な引き戻し正方形での成分ごとの終対象性。
方針：元の頂点を標準引き戻しへ同型で移し、写像空間の判定を使う。
規約：元の正方形の射影と頂点を保持する。
使われ方：錐族の引き戻し正方形から極限錐を判定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：inner fibration を一脚とする引き戻しの三成分が終対象なら元の頂点も終対象。
方針：標準引き戻しとの同型で三成分を照合し、写像空間の可縮性を使う。
規約：元の頂点 x の終対象性を結論する。
使われ方：引き戻し内の図式の成分ごとの極限錐判定。 -/
lemma isTerminalVertex_of_isPullback_of_components {W E D B : SSet.{u}}
    [Quasicategory W] [Quasicategory E] [Quasicategory D] [Quasicategory B]
    {a : W ⟶ E} {b : W ⟶ D} {p : E ⟶ B} {q : D ⟶ B}
    (s : IsPullback a b p q) [InnerFibration p] (x : W _⦋0⦌)
    (he : IsTerminalVertex (a.app (Opposite.op ⦋0⦌) x))
    (hd : IsTerminalVertex (b.app (Opposite.op ⦋0⦌) x))
    (hb : IsTerminalVertex ((a ≫ p).app (Opposite.op ⦋0⦌) x)) :
    IsTerminalVertex x := by
  apply ((qCatEquivalenceOfIso s.isoPullback).isTerminalVertex_iff x).2
  apply isTerminalVertex_pullback_of_components p q (fun _ _ ↦ inferInstance)
  · change IsTerminalVertex
      ((s.isoPullback.hom ≫ pullback.fst p q).app (Opposite.op ⦋0⦌) x)
    rw [s.isoPullback_hom_fst]
    exact he
  · change IsTerminalVertex
      ((s.isoPullback.hom ≫ pullback.snd p q).app (Opposite.op ⦋0⦌) x)
    rw [s.isoPullback_hom_snd]
    exact hd
  · change IsTerminalVertex
      (((s.isoPullback.hom ≫ pullback.fst p q) ≫ p).app (Opposite.op ⦋0⦌) x)
    rw [s.isoPullback_hom_fst]
    exact hb

end SerrePositivity.InfinityCategories.F2
