module

public import SerrePositivity.InfinityCategories.F1B.KanJoinShiftPrism

/-!
概要：join の切断より前で区間を短くするときの補った単体の制限。
方針：切断の一意性で制限後の切断を求め、左右の順序写像を比較する。
規約：空区間を含む頂点数の表示を使う。
使われ方：join の移動 prism の係数の可換性の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：切断より前の先頭区間では、全ての頂点が左側にある。
方針：各頂点の所属による切断の一意性。
規約：空区間を許す。
使われ方：先頭制限での join の左因子の復元。 -/
lemma kanJoin_pullCut_prefix (r l m : ℕ) (hl : l ≤ r) (hm : m ≤ l) :
    Join.pullCut (Join.prefixIncl r m (hm.trans hl)) l = m := by
  apply Join.cut_ext (Join.pullCut_le _ _) (by rfl)
  intro i
  rw [Join.lt_pullCut_iff]
  change i.val < l ↔ i.val < m
  have := i.isLt
  omega

/-- 概要：切断より前の m 頂点を除くと切断は l−m となる。
方針：末尾区間の添字の原点移動を切断の特徴づけに代入する。
規約：m=l も含む。
使われ方：残った二因子の join の係数の復元。 -/
lemma kanJoin_pullCut_suffix (r l m : ℕ) (hl : l ≤ r) (hm : m ≤ l) :
    Join.pullCut (Join.suffixIncl r m (hm.trans hl)) l = l - m := by
  apply Join.cut_ext (Join.pullCut_le _ _) (by omega)
  intro i
  rw [Join.lt_pullCut_iff]
  change m + i.val < l ↔ i.val < l - m
  omega

/-- 概要：切断より前の先頭制限は左因子の先頭制限の包含。
方針：補った join の自然性と切断の計算を使い、空の右因子を消す。
規約：全次数で成り立つ。
使われ方：prism の第一の係数の比較。 -/
lemma kanAugJoin_prefix {A B : SSet.{u}} (r : ℕ) (s : StableAugJoin A B r)
    (m : ℕ) (hm : m ≤ s.1.val) :
    Join.augMap (join A B) (Join.prefixIncl r m (hm.trans (Nat.le_of_lt_succ s.1.isLt)))
      ((stableAugJoinEquiv A B r).symm s) =
      Join.augHom (joinInl A B) m
        (Join.augMap A (Join.prefixIncl s.1.val m hm) s.2.1) := by
  apply (stableAugJoinEquiv A B m).injective
  rw [stableAugJoinEquiv_naturality, Equiv.apply_symm_apply, stableAugJoinEquiv_inl]
  have hc := kanJoin_pullCut_prefix r s.1.val m (Nat.le_of_lt_succ s.1.isLt) hm
  apply stableAugJoin_hext
  · exact hc
  · exact stableAugMap_heq A hc rfl _ _ (by intro i j hij; exact hij) _ _ HEq.rfl
  · refine (stableAugEmpty_heq B
      (by omega : m - Join.pullCut (Join.prefixIncl r m _) s.1.val = 0)
      (Join.augMap B (Join.rightMap (Join.prefixIncl r m _) s.1.val) s.2.2)).trans ?_
    exact (stableAugEmpty_heq B (Nat.sub_self m)
      (stableAugJoinInl A B m (Join.augMap A (Join.prefixIncl s.1.val m hm) s.2.1)).2.2).symm

/-- 概要：切断より前で先頭を取り除いた join の切断表示。
方針：切断は l−m、左因子はその末尾制限、右因子は元のままと計算する。
規約：最後の因子の頂点数の等式に沿う移送を明示する。
使われ方：prism の結合同型で得る第二の係数の比較。 -/
lemma kanAugJoin_suffix {A B : SSet.{u}} (r : ℕ) (s : StableAugJoin A B r)
    (m : ℕ) (hm : m ≤ s.1.val) :
    stableAugJoinEquiv A B (r - m)
      (Join.augMap (join A B) (Join.suffixIncl r m (hm.trans (Nat.le_of_lt_succ s.1.isLt)))
        ((stableAugJoinEquiv A B r).symm s)) =
      ⟨⟨s.1.val - m, by have := s.1.isLt; omega⟩,
        Join.augMap A (Join.suffixIncl s.1.val m hm) s.2.1,
        cast (congrArg (Join.augObj B) (by omega : r - s.1.val = r - m - (s.1.val - m)))
          s.2.2⟩ := by
  rw [stableAugJoinEquiv_naturality, Equiv.apply_symm_apply]
  have hc := kanJoin_pullCut_suffix r s.1.val m (Nat.le_of_lt_succ s.1.isLt) hm
  apply stableAugJoin_hext
  · exact hc
  · exact stableAugMap_heq A hc rfl _ _ (by
      intro i j hij
      change m + i.val = m + j.val
      omega) _ _ HEq.rfl
  · have h := stableAugMap_heq B (by rw [hc]; omega :
        r - m - Join.pullCut (Join.suffixIncl r m (hm.trans (Nat.le_of_lt_succ s.1.isLt)))
          s.1.val = r - s.1.val) rfl
      (Join.rightMap (Join.suffixIncl r m (hm.trans (Nat.le_of_lt_succ s.1.isLt))) s.1.val)
      OrderHom.id (by
        intro i j hij
        change m + (Join.pullCut (Join.suffixIncl r m _) s.1.val + i.val) - s.1.val = j.val
        omega) s.2.2 s.2.2 HEq.rfl
    rw [Join.augMap_id] at h
    exact h.trans (cast_heq _ _).symm

end SerrePositivity.InfinityCategories
