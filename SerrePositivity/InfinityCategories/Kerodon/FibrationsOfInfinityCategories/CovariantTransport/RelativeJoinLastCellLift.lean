module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinStdSimplexRightTail

/-!
概要：右成分が終端に固定された join の単体の最後の prism セルへの持ち上げ。
方針：左区間の順序写像に最後の頂点の定値写像を連結し、比較像の頂点番号を計算する。
規約：f は標準単体間の射で最後の頂点を保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界と prism による relative join の被覆。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：join の左の単体を最後の prism セルの単体へ延長する。
方針：左区間の係数の順序写像に m+1 番目の頂点の定値部分を連結する。
規約：右成分はこの構成では読まず、切断位置だけを使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後のセルの被覆の具体的な持ち上げ。 -/
noncomputable def relativeJoinLastCellLiftSimplex {m n d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d) : (Δ[m + 1] : SSet.{u}) _⦋d⦌ :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) (OrderHom.const _ (0 : Fin 1))))

/-- 概要：右成分が終端なら、最後のセルへの持ち上げの比較像は元の join の単体に一致する。
方針：左区間と右区間の頂点番号を比較し、標準単体の外延性を使う。
規約：通常の join への第一射影についての等式を結論する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の被覆の持ち上げの検証。 -/
lemma relativeJoinLastCellLiftSimplex_fst {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d)
    (hs : ∀ j : Fin (d + 1 - s.1.val), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ s.2.2 j = Fin.last n) :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n])).app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌)
        ((SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m (Fin.last m))).app
          (Opposite.op ⦋d⦌) (relativeJoinLastCellLiftSimplex s))) = s := by
  apply (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} m n).hom.app (Opposite.op ⦋d⦌))).mp
    inferInstance
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_lastCell_stdSimplex_val f hf]
  by_cases hi : i.val < s.1.val
  · let j : Fin s.1.val := ⟨i.val, hi⟩
    have ha : (relativeJoinLastCellLiftSimplex s i).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1 j).val := by
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt s.1.val (Nat.le_of_lt_succ s.1.isLt)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) (OrderHom.const _ (0 : Fin 1)) i hi
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_join_prefix_val s j
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} m n).hom.app (Opposite.op ⦋d⦌) s i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1 j).val at hv
    rw [ha, ite_eq_left (Nat.le_of_lt_succ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1 j).isLt)]
    exact hv.symm
  · let j : Fin (d + 1 - s.1.val) := ⟨i.val - s.1.val, by have := i.isLt; omega⟩
    have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) j = i := by
      apply Fin.ext
      change s.1.val + (i.val - s.1.val) = i.val
      omega
    have ha : (relativeJoinLastCellLiftSimplex s i).val = m + 1 := by
      have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge s.1.val (Nat.le_of_lt_succ s.1.isLt)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) (OrderHom.const _ (0 : Fin 1)) i (Nat.le_of_not_lt hi)
      exact he
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_join_suffix_val s j
    rw [hq, hs j] at hv
    rw [ha, ite_eq_right (by omega)]
    exact hv.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
