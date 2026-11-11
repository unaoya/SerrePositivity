module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：通常の join の円柱比較の単体ごとの式。
方針：区間の join 表示の切断を使い、左右の成分を先頭・末尾へ制限する。
規約：点との直積の補った単体の射影を明示する。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の比較と切断。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：補った直積の第二成分の射影は元の第二単体を返す。
方針：空次数は一意性、非空次数は直積の計算を使う。
規約：r は頂点数。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱比較の右成分の計算。 -/
lemma Join.augTensorEquiv_symm_augHomSnd (A B : SSet.{u}) (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (snd A B) r ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv A B r).symm (a, b)) = b := by
  cases r with
  | zero => cases b; rfl
  | succ r => rfl

/-- 概要：join の円柱比較の単体は区間の切断で左右の成分を制限したもの。
方針：左右の直積との比較と最後の射影を計算する。
規約：a と b は同じ次数 n の単体、t は標準区間の単体。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の比較。 -/
lemma joinCylinderMap_app (A B : SSet.{u}) (n : ℕ)
    (a : A _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) (b : B _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap A B).app (Opposite.op ⦋n⦌) ((a, t), b) =
      let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
      (⟨s.1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) s.1.val
          (Nat.le_of_lt_succ s.1.isLt)) a,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (n + 1) s.1.val
          (Nat.le_of_lt_succ s.1.isLt)) b⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) := by
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  change (⟨s.1,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (fst A (Δ[0] : SSet.{u})) s.1.val
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv A (Δ[0] : SSet.{u}) s.1.val).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) s.1.val _) a, s.2.1)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (snd (Δ[0] : SSet.{u}) B) (n + 1 - s.1.val)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv (Δ[0] : SSet.{u}) B (n + 1 - s.1.val)).symm
        (s.2.2, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (n + 1) s.1.val _) b))⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augTensorEquiv_symm_augHomFst, Join.augTensorEquiv_symm_augHomSnd]

/-- 概要：区間を二点の join に戻すと切断は値零の逆像の大きさ。
方針：標準単体の join の逆写像の定義を読む。
規約：値零の条件は Fin 2 で一未満という条件。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱の区間の切断。 -/
lemma intervalJoin_cut (n : ℕ) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t).1.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 := rfl

/-- 概要：標準単体の join の円柱比較は区間の零側で左の値、一側で右の値を読む。
方針：区間の切断の左右で順序写像の連結を計算する。
規約：右側の値には左の頂点数 n+1 を加える。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の切断の構成と正規化との同一視。 -/
lemma joinCylinderMap_stdSimplex_val (n m d : ℕ)
    (a : (Δ[n] : SSet.{u}) _⦋d⦌) (t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (b : (Δ[m] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom.app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[n] Δ[m]).app (Opposite.op ⦋d⦌) ((a, t), b)) i).val =
        if (t i).val = 0 then (a i).val else n + 1 + (b i).val := by
  rw [joinCylinderMap_app]
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋d⦌) t
  have hs : s.1.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 := intervalJoin_cut d t
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Δ[n] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) s.1.val _) a))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Δ[m] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val _) b)) i).val = _
  by_cases ht : (t i).val = 0
  · have hi : i.val < s.1.val := by
      rw [hs]
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff _ _ i).mpr
      change (t i).val < 1
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv_augMap, if_pos ht]
    rfl
  · have hi : s.1.val ≤ i.val := by
      rw [hs]
      apply Nat.le_of_not_lt
      intro h
      have ht' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 i).mp h
      change (t i).val < 1 at ht'
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv_augMap, if_neg ht]
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)
        ⟨i.val - s.1.val, by have := i.isLt; omega⟩ = i := Fin.ext (by
      change s.1.val + (i.val - s.1.val) = i.val
      omega)
    rw [he]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
