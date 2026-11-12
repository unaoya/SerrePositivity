module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.AssociativeJoinSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociativityCuts

/-!
概要：join の長さの和による表示に単体作用を移す。
方針：切断の逆像と左右の制限を使い、空を補った join の単体作用との一致を示す。
規約：頂点数零を含む順序写像について検証する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の反復 slice に使う join の結合の自然性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：長さの和で表した join の単体を順序写像で引き戻す。
方針：左の長さを切断の逆像に置き換え、左右の単体を制限する。
規約：右区間の長さの等式による移送を明示する。
使われ方：Kerodon §4.3.5（Tag 017V） の join の再結合の単体作用。 -/
def joinSumSimplexMap (A B : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B m := by
  rintro ⟨⟨a, b, x, y⟩, h⟩
  change a + b = n at h
  refine ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a, m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α a) x,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a)
      (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B) (by omega : b = n - a)) y)⟩, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + (m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a) = m
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α a
  omega

/-- 概要：join の長さの和による全単射は全ての単体作用と可換。
方針：空の始域と終域を分け、非空の場合は join の定義に戻す。
規約：この同定は二因子の表示の自然性。三因子の再結合の自然性は後続。
使われ方：HTT §1.2.8 の join の結合の単体的自然性を証明する準備。 -/
lemma augmentedJoinSumEquiv_map (A B : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) α s) =
      joinSumSimplexMap A B α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n s) := by
  cases m with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    cases n with
    | zero => exact Fin.elim0 (α 0)
    | succ n =>
      rcases s with ⟨a, x, y⟩
      rfl

/-- 概要：長さの和表示の単体作用は恒等写像で恒等となる。
方針：join の補った単体への全単射で戻し、既存の恒等則を移す。
規約：頂点数零も含む。
使われ方：Kerodon §4.3.5（Tag 017V） の再結合の共通表示の単体的構造。 -/
lemma joinSumSimplexMap_id (A B : SSet.{u}) (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n) :
    joinSumSimplexMap A B (OrderHom.id : Fin n →o Fin n) s = s := by
  obtain ⟨t, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n).surjective s
  rw [← augmentedJoinSumEquiv_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_id]

/-- 概要：長さの和表示の単体作用は順序写像の合成に反変的。
方針：補った join の単体に戻し、自然性を介して既存の合成則を使う。
規約：空を含む全ての頂点数の組で成立する。
使われ方：HTT §1.2.8 の join の結合の共通表示の関手性。 -/
lemma joinSumSimplexMap_comp (A B : SSet.{u}) {l m n : ℕ}
    (α : Fin m →o Fin n) (β : Fin l →o Fin m) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n) :
    joinSumSimplexMap A B (α.comp β) s =
      joinSumSimplexMap A B β (joinSumSimplexMap A B α s) := by
  obtain ⟨t, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n).surjective s
  rw [← augmentedJoinSumEquiv_map, ← augmentedJoinSumEquiv_map,
    ← augmentedJoinSumEquiv_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
