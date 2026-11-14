module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiniteJoinPieces

/-!
概要：両因子と非退化単体の対の標準 join の像は join 全体を被覆する。
方針：単体を左右の頂点数で分け、非空の両成分をそれぞれ非退化分解する。
規約：空の因子は元の因子の包含で処理する。
使われ方：有限 join の有限部分複体による表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：左右の頂点数で表示した単体は被覆のいずれかの部品に属する。
方針：空の片側を除き、両成分の非退化分解を joinMap で貼る。
規約：左右の頂点数の和を入力とする。使われ方：join 全体の被覆の点ごとの証明。 -/
lemma mkOfSum_mem_finiteJoinPiece {K L : SSet.{u}} {n l r : ℕ}
    (h : l + r = n + 1) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K l) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L r) :
    ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h a b ∈ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteJoinPiece K L i).obj (Opposite.op ⦋n⦌) := by
  cases l with
  | zero =>
    have hr : r = n + 1 := by omega
    subst r
    refine ⟨.inr (.inl ()), b, ?_⟩
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext <;> try rfl
  | succ l =>
    cases r with
    | zero =>
      have hl : l = n := by omega
      subst l
      exact ⟨.inl (), a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_zero_right h a b).symm⟩
    | succ r =>
      obtain ⟨ka, x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.simplex_in_nondegenerate_range (K := K) a
      obtain ⟨lb, y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.simplex_in_nondegenerate_range (K := L) b
      refine ⟨.inr (.inr (ka, lb)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h x y, ?_⟩
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mkOfSum]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum h ((SSet.yonedaEquiv.symm ka.simplex).app _ x)
        ((SSet.yonedaEquiv.symm lb.simplex).app _ y) = _
      rw [hx, hy]

/-- 概要：join の被覆部分複体の上限は全体。
方針：任意の単体を頂点数による表示へ戻し、部品への所属を使う。
規約：有限性はまだ仮定しない。使われ方：有限被覆による有限性の判定。 -/
lemma iSup_finiteJoinPiece (K L : SSet.{u}) : ⨆ i, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteJoinPiece K L i = ⊤ := by
  apply le_antisymm le_top
  intro n s _
  obtain ⟨⟨n⟩⟩ := n
  obtain ⟨i, hi⟩ := mkOfSum_mem_finiteJoinPiece (K := K) (L := L) (n := n)
    (by
      change s.1.val + (n + 1 - s.1.val) = n + 1
      have hs : s.1.val < n + 2 := s.1.isLt
      omega) s.2.1 s.2.2
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum_eta] at hi
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨i, hi⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
