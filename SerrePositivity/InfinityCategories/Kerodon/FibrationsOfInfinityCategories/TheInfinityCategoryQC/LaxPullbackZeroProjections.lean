module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackZeroVertices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：零対象を保つ二関手の lax pullback の両射影は零対象を保つ。
方針：一つの零頂点の像の零性を全ての零頂点へ同型で輸送する。
規約：選択された零対象だけの保存に条件を弱めない。
使われ方：Tamme Lemma 8(iv) の射影の完全性への入力。

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

/-- 概要：一つの零頂点を零頂点へ写す関手は全ての零頂点を保つ。
方針：零頂点の一意な同型を関手で写し、零性を輸送する。
規約：両圏の安定性は要求しない。
使われ方：lax pullback の射影の零保存。 -/
lemma preservesZeroVertices_of_one_zero {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex x)
    (hf : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.app (Opposite.op ⦋0⦌) x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices f := by
  intro y hy
  exact hf.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso hx.2 hy.2) f)

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：lax pullback の第一射影は全ての零対象を保つ。
方針：両成分が零である零頂点の存在と同型による零保存の判定を使う。
規約：元の二関手は零対象を保つと仮定する。
使われ方：第一射影の完全性の零保存条件。 -/
lemma laxPullbackFst_preservesZero (p : A ⟶ C) (q : B ⟶ C)
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex B]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q) := by
  obtain ⟨x, hx, ha, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exists_zeroVertex_laxPullback_with_components p q hp hq
  exact preservesZeroVertices_of_one_zero _ x hx ha

/-- 概要：lax pullback の第二射影は全ての零対象を保つ。
方針：両成分が零である零頂点の存在と同型による零保存の判定を使う。
規約：元の二関手は零対象を保つと仮定する。
使われ方：第二射影の完全性の零保存条件。 -/
lemma laxPullbackSnd_preservesZero (p : A ⟶ C) (q : B ⟶ C)
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex B]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q) := by
  obtain ⟨x, hx, _, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exists_zeroVertex_laxPullback_with_components p q hp hq
  exact preservesZeroVertices_of_one_zero _ x hx hb

/-- 概要：lax pullback の零対象性は両入力の零対象性と同値。
方針：両射影の零保存と、成分ごとの始終対象の判定を合わせる。
規約：元の二関手が零対象を保つ条件を明示する。
使われ方：零角の四角形の成分表示。 -/
lemma isZeroVertex_laxPullback_iff (p : A ⟶ C) (q : B ⟶ C)
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex B]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices q)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex x ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x) ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x) :=
  ⟨fun hx ↦ ⟨laxPullbackFst_preservesZero p q hp hq x hx,
      laxPullbackSnd_preservesZero p q hp hq x hx⟩,
    fun ⟨ha, hb⟩ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isZeroVertex_laxPullback_of_components p q x ha hb (hp _ ha) (hq _ hb)⟩

/-- 概要：完全な二関手の lax pullback は零対象を持つ。
方針：完全性に含まれる零保存を既存の存在判定へ渡す。
規約：安定性の存在を仮定せず pointed 条件だけを導く。
使われ方：Tamme Lemma 8(iv) の安定性の最初の条件。 -/
instance laxPullback_hasZeroVertex (p : A ⟶ C) (q : B ⟶ C)
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor p] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.hasZeroVertex_laxPullback_of_preservesZero p q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
