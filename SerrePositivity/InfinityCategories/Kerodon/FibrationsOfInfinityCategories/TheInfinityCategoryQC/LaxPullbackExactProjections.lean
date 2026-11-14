module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackZeroSpanColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackSquareCriteria

/-!
概要：安定圏間の完全関手の lax pullback の両射影は完全。
方針：零角の span の入力の余極限の存在から成分判定を使い、零保存と cofiber 保存を示す。
規約：lax pullback 自身の安定性を仮定しない。
使われ方：Tamme Lemma 8(iv) の完全な二射影。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (p : A ⟶ C) (q : B ⟶ C)
variable [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor p] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q]

/-- 概要：零角の四角形の押し出し性は両入力の四角形の押し出し性と同値。
方針：零枝を持つ元の span の入力に余極限が存在することを使う。
規約：元の指定された零角を保つ。
使われ方：cofiber 列の射影による保存と反映。 -/
lemma isPushoutSquare_laxPullback_iff_of_zero_corner (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q) := by
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact t.zero_corner
  obtain ⟨ha, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullback_span_input_colimits_of_zero_second p q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square) hz
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isPushoutSquare_laxPullback_iff_of_input_colimits p q t.square ha hb

/-- 概要：lax pullback の第一射影は零対象と cofiber 列を保つ完全関手。
方針：既存の零保存と零角の押し出し四角形の成分判定を使う。
規約：始域の安定性は仮定しない。
使われ方：Tamme Lemma 8(iv) の第一の完全射影。 -/
instance laxPullbackFst_isExactFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackFst_preservesZero p q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q))
  preservesCofiber t ht := ((isPushoutSquare_laxPullback_iff_of_zero_corner p q t).1 ht).1

/-- 概要：lax pullback の第二射影は零対象と cofiber 列を保つ完全関手。
方針：既存の零保存と零角の押し出し四角形の成分判定を使う。
規約：始域の安定性は仮定しない。
使われ方：Tamme Lemma 8(iv) の第二の完全射影。 -/
instance laxPullbackSnd_isExactFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackSnd_preservesZero p q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q))
  preservesCofiber t ht := ((isPushoutSquare_laxPullback_iff_of_zero_corner p q t).1 ht).2

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Lemma 8" (partial := component) "仮定：各射影に沿う余極限を脚が保つ設定と、安定性については完全な二脚（原典の (i)、(ii)、(iv) の仮定）。結論：lax 引き戻し上の余極限と射影による保存、両入力が冪等完備なら lax 引き戻しも冪等完備、さらに安定性と二つの射影の完全性（原典の (i)、(ii)、(iv) の lax 側）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackFst_isExactFunctor
attribute [cite Tamme "Lemma 8" (partial := component) "仮定：各射影に沿う余極限を脚が保つ設定と、安定性については完全な二脚（原典の (i)、(ii)、(iv) の仮定）。結論：lax 引き戻し上の余極限と射影による保存、両入力が冪等完備なら lax 引き戻しも冪等完備、さらに安定性と二つの射影の完全性（原典の (i)、(ii)、(iv) の lax 側）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackSnd_isExactFunctor
