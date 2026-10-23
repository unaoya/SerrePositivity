module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackFibers
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCofibers

/-!
概要：安定圏間の完全関手の lax pullback は安定な ∞ 圏となる。
方針：零角の引き戻し性と押し出し性を両成分で判定し、入力の安定性で比較する。
規約：元の三圏の安定性と二関手の完全性のみを仮定する。
使われ方：Tamme Lemma 8(iv) と dg gluing の安定圏への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [IsStable A] [IsStable B] [IsStable C] (p : A ⟶ C) (q : B ⟶ C)
variable [IsExactFunctor p] [IsExactFunctor q]

/-- 概要：零角の四角形の引き戻し性は両入力の引き戻し性と同値。
方針：第二枝が零対象から出る入力 cospan の極限存在を使う。
規約：元の零角を保ち、lax pullback の安定性は前提にしない。
使われ方：fiber 列の両射影による保存と反映。 -/
lemma isPullbackSquare_laxPullback_iff_of_zero_corner (t : ZeroTriangle (laxPullback p q)) :
    IsPullbackSquare t.square ↔ IsPullbackSquare (t.square ≫ laxPullbackFst p q) ∧
      IsPullbackSquare (t.square ≫ laxPullbackSnd p q) := by
  have hz : IsZeroVertex ((horn₂₂.ι₁₂ ≫ pullbackCospan t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge]
    exact t.zero_corner
  obtain ⟨ha, hb⟩ := laxPullback_cospan_input_limits_of_zero_second p q
    (pullbackCospan t.square) hz
  exact isPullbackSquare_laxPullback_iff_of_input_limits p q t.square ha hb

/-- 概要：lax pullback の零角四角形は fiber 列であることと cofiber 列であることが同値。
方針：両成分の安定性による同値を零角の成分判定の間に挟む。
規約：元の四角形そのものを比較する。
使われ方：安定性の第三条件。 -/
lemma laxPullback_fiber_iff_cofiber (t : ZeroTriangle (laxPullback p q)) :
    IsFiberSequence t ↔ IsCofiberSequence t := by
  let ta := t.map (laxPullbackFst p q) (IsExactFunctor.preservesZero (F := laxPullbackFst p q))
  let tb := t.map (laxPullbackSnd p q) (IsExactFunctor.preservesZero (F := laxPullbackSnd p q))
  exact (isPullbackSquare_laxPullback_iff_of_zero_corner p q t).trans
    ((and_congr (IsStable.fiber_iff_cofiber ta) (IsStable.fiber_iff_cofiber tb)).trans
      (isPushoutSquare_laxPullback_iff_of_zero_corner p q t).symm)

/-- 概要：安定圏間の完全関手の lax pullback は安定。
方針：零対象、全ての射の fiber と cofiber、零角の列の一致を合成する。
規約：lax pullback の有限完備性や安定性を仮定しない。
使われ方：Tamme Lemma 8(iv) の安定な貼り合わせ圏。 -/
instance laxPullback_isStable : IsStable (laxPullback p q) where
  toHasZeroVertex := inferInstance
  fiber_exists := laxPullback_fiber_exists p q
  cofiber_exists := laxPullback_cofiber_exists p q
  fiber_iff_cofiber := laxPullback_fiber_iff_cofiber p q

end SerrePositivity.InfinityCategories.F2
