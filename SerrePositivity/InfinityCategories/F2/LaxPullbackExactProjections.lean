module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackZeroSpanColimits
public import SerrePositivity.InfinityCategories.F2.LaxPullbackSquareCriteria

/-!
概要：安定圏間の完全関手の lax pullback の両射影は完全。
方針：零角の span の入力の余極限の存在から成分判定を使い、零保存と cofiber 保存を示す。
規約：lax pullback 自身の安定性を仮定しない。
使われ方：Tamme Lemma 8(iv) の完全な二射影。
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

/-- 概要：零角の四角形の押し出し性は両入力の四角形の押し出し性と同値。
方針：零枝を持つ元の span の入力に余極限が存在することを使う。
規約：元の指定された零角を保つ。
使われ方：cofiber 列の射影による保存と反映。 -/
lemma isPushoutSquare_laxPullback_iff_of_zero_corner (t : ZeroTriangle (laxPullback p q)) :
    IsPushoutSquare t.square ↔ IsPushoutSquare (t.square ≫ laxPullbackFst p q) ∧
      IsPushoutSquare (t.square ≫ laxPullbackSnd p q) := by
  have hz : IsZeroVertex ((horn₂₀.ι₀₂ ≫ pushoutSpan t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
    exact t.zero_corner
  obtain ⟨ha, hb⟩ := laxPullback_span_input_colimits_of_zero_second p q (pushoutSpan t.square) hz
  exact isPushoutSquare_laxPullback_iff_of_input_colimits p q t.square ha hb

/-- 概要：lax pullback の第一射影は零対象と cofiber 列を保つ完全関手。
方針：既存の零保存と零角の押し出し四角形の成分判定を使う。
規約：始域の安定性は仮定しない。
使われ方：Tamme Lemma 8(iv) の第一の完全射影。 -/
instance laxPullbackFst_isExactFunctor : IsExactFunctor (laxPullbackFst p q) where
  preservesZero := laxPullbackFst_preservesZero p q
    (IsExactFunctor.preservesZero (F := p)) (IsExactFunctor.preservesZero (F := q))
  preservesCofiber t ht := ((isPushoutSquare_laxPullback_iff_of_zero_corner p q t).1 ht).1

/-- 概要：lax pullback の第二射影は零対象と cofiber 列を保つ完全関手。
方針：既存の零保存と零角の押し出し四角形の成分判定を使う。
規約：始域の安定性は仮定しない。
使われ方：Tamme Lemma 8(iv) の第二の完全射影。 -/
instance laxPullbackSnd_isExactFunctor : IsExactFunctor (laxPullbackSnd p q) where
  preservesZero := laxPullbackSnd_preservesZero p q
    (IsExactFunctor.preservesZero (F := p)) (IsExactFunctor.preservesZero (F := q))
  preservesCofiber t ht := ((isPushoutSquare_laxPullback_iff_of_zero_corner p q t).1 ht).2

end SerrePositivity.InfinityCategories.F2
