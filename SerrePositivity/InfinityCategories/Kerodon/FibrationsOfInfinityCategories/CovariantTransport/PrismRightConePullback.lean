module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrismRightConeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrismRightConeRange

/-!
概要：prism と対角の右錐の比較の正方形の pullback 性。
方針：最後の面からの join の像で欠ける頂点を使って時刻の条件を取り出し、右錐へ戻す。
規約：全ての次数で型の pullback の持ち上げを構成する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の右錐の比較の同型性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：最後の面の包含は補った単体の頂点番号を変えない。
方針：非空区間では最後の面の順序写像が castSucc であることを使う。
規約：r は頂点数、空区間には頂点がない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、左の最後の頂点が像から欠けることの計算。 -/
lemma prismRightCone_lastFace_aug_val {n r : ℕ}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[n] : SSet.{u}) r) (i : Fin r) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv (n + 1) r
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.δ (Fin.last (n + 1))) r a) i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n r a i).val := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    change (Δ[n] : SSet.{u}) _⦋r⦌ at a
    change (((stdSimplex.δ (Fin.last (n + 1))).app (Opposite.op ⦋r⦌) a) i).val = (a i).val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_hom_apply]
    change ((Fin.last (n + 1)).succAbove (a i)).val = (a i).val
    rw [Fin.succAbove_last]
    rfl

/-- 概要：左の最後の面の包含を join に適用した像は左側の最後の頂点を避ける。
方針：切断前の値は n 以下、切断後の値は n+2 以上であることを使う。
規約：通常の join を標準単体と同定して頂点番号を読む。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の係数で時刻零が現れないことの検査。 -/
lemma prismRightCone_joinFace_avoids_left_last {n d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[n] : SSet.{u}) Δ[n + 1] d) (i : Fin (d + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])).app
        (Opposite.op ⦋d⦌) s) i).val ≠ n + 1 := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])).app
    (Opposite.op ⦋d⦌) s
  by_cases hi : i.val < s.1.val
  · let j : Fin s.1.val := ⟨i.val, hi⟩
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_join_prefix_val a j
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌) a i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv (n + 1) s.1.val
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.δ (Fin.last (n + 1))) s.1.val s.2.1) j).val at he
    rw [prismRightCone_lastFace_aug_val] at he
    have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n s.1.val s.2.1 j).isLt
    intro hh
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌) a i).val = n + 1 at hh
    omega
  · let j : Fin (d + 1 - s.1.val) := ⟨i.val - s.1.val, by have := i.isLt; omega⟩
    have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) j = i := by
      apply Fin.ext
      change s.1.val + (i.val - s.1.val) = i.val
      omega
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_join_suffix_val a j
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌) a
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) j)).val =
        (n + 1) + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv (n + 1) _ a.2.2 j).val at he
    rw [hq] at he
    intro hh
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌) a i).val = n + 1 at hh
    omega

/-- 概要：prism の右錐の比較と対角の右錐の正方形は pullback。
方針：欠ける左頂点から最後の係数の時刻条件を得て、prism の右錐への持ち上げを使う。
規約：右辺の最後の面の join の包含と左辺の比較は共に単射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐を取った定義の pullback との貼り合わせ。 -/
lemma prismRightCone_isPullback (n : ℕ) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal.{u} n) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n + 1]) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨d⟩⟩
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦ k.app (Opposite.op ⦋d⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightCone_square n), ?_, ?_⟩
  · intro x y h
    exact (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap.{u} n).app (Opposite.op ⦋d⦌))).mp
      inferInstance h.2
  · rintro s ⟨t, c⟩ h
    have ht : ∀ i : Fin (d + 1), c i = Fin.last (n + 1) → t i = 1 := by
      intro i hi
      apply Fin.ext
      change (t i).val = 1
      have hb := (t i).isLt
      by_contra hn
      have h₀ : (t i).val = 0 := by omega
      have he := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[n + 1] : SSet.{u}) Δ[n + 1] d ↦
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌) z i).val) h
      have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_stdSimplex_val (n + 1) d t c i
      rw [ite_eq_left h₀, hi] at hd
      exact prismRightCone_joinFace_avoids_left_last s i (he.trans hd)
    obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap_mem_range t c ht
    refine ⟨z, ?_, hz⟩
    apply (mono_iff_injective
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 (Δ[n + 1] : SSet.{u}))).app
        (Opposite.op ⦋d⦌))).mp inferInstance
    have he := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦ k.app (Opposite.op ⦋d⦌) z)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightCone_square n)
    exact he.trans ((congrArg (fun w ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[n + 1] : SSet.{u})).app
      (Opposite.op ⦋d⦌) w) hz).trans h.symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
