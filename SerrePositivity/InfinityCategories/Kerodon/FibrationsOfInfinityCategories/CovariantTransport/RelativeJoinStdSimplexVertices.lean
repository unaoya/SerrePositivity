module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPrismLastCellMono
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalStdSimplex

/-!
概要：標準単体上の relative join の被覆で使う join の左右の頂点の式。
方針：join の有限順序集合の連結の式を、先頭区間と末尾区間で評価する。
規約：頂点数零も許す補った標準単体を使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界に入らない単体の右成分の固定。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：標準単体間の射の単体への作用は頂点の順序写像の合成。
方針：Yoneda の対応で射をその恒等単体での値へ戻して評価する。
規約：射の頂点写像は SSet.yonedaEquiv f とする。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の頂点の像の条件の利用。 -/
lemma relativeJoin_stdSimplex_hom_apply {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (a : (Δ[m] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    f.app (Opposite.op ⦋d⦌) a i = (SSet.yonedaEquiv f) (a i) := by
  calc
    _ = (SSet.yonedaEquiv.symm (SSet.yonedaEquiv f)).app (Opposite.op ⦋d⦌) a i := by
      rw [Equiv.symm_apply_apply]
    _ = _ := rfl

/-- 概要：補った標準単体への射の頂点での作用も頂点写像の合成で与えられる。
方針：空次数を除外し、非空次数で通常の頂点の式を使う。
規約：r は頂点数。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、join の左成分への構造射の作用。 -/
lemma relativeJoin_stdAugHom_apply {m n r : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[m] : SSet.{u}) r) (i : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f r a) i =
      (SSet.yonedaEquiv f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m r a i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact relativeJoin_stdSimplex_hom_apply f a i

/-- 概要：標準単体の join の先頭区間の頂点番号は左成分の頂点番号。
方針：有限順序集合の連結を切断より前で評価する。
規約：先頭区間の頂点を全体の同じ番号へ含める。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、左の最後の頂点の像の比較。 -/
lemma relativeJoin_stdSimplex_join_prefix_val {m n d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d) (i : Fin s.1.val) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌) s
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1 i).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ s.2.2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i).val < s.1.val
      from i.isLt)]
  rfl

/-- 概要：標準単体の join の末尾区間の頂点番号は右成分の番号を左頂点数だけずらしたもの。
方針：有限順序集合の連結を切断以降で評価する。
規約：末尾区間の頂点の全体での番号は切断と局所番号の和。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右成分と底の単体の比較。 -/
lemma relativeJoin_stdSimplex_join_suffix_val {m n d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d) (i : Fin (d + 1 - s.1.val)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌) s
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i)).val =
      m + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ s.2.2 i).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ s.2.2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ (by change s.1.val ≤ s.1.val + i.val; omega)]
  apply congrArg (fun j : Fin (d + 1 - s.1.val) ↦
    m + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ s.2.2 j).val)
  apply Fin.ext
  change s.1.val + i.val - s.1.val = i.val
  omega

/-- 概要：左の境界との join に入らない単体の左成分は全頂点を通る。
方針：欠ける頂点があれば左成分が境界に入り、元の単体が境界の join から来ることを使う。
規約：左成分は空区間を補った有限順序写像として読む。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、左成分の最後の頂点を選ぶ段階。 -/
lemma relativeJoin_not_left_boundary_surjective {Y : SSet.{u}} {m d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[m] : SSet.{u}) Y d)
    (hs : s ∉ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) := by
  classical
  by_contra hn
  apply hs
  rcases s with ⟨⟨l, hl⟩, a, b⟩
  cases l with
  | zero =>
    exact ⟨⟨⟨0, hl⟩, PUnit.unit, b⟩, by
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (by rfl) ?_ ?_
      · cases a; rfl
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id Y _ b⟩
  | succ l =>
    change (Δ[m] : SSet.{u}) _⦋l⦌ at a
    change ¬ ∀ v : Fin (m + 1), ∃ i : Fin (l + 1), a i = v at hn
    have ha : a ∈ (boundary m).obj (Opposite.op ⦋l⦌) := by
      rw [mem_boundary_iff_notMem_range]
      simpa only [Set.mem_range, not_forall, not_exists] using hn
    refine ⟨⟨⟨l + 1, hl⟩, ⟨a, ha⟩, b⟩, ?_⟩
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (by rfl) ?_ ?_
    · rfl
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id Y _ b

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
