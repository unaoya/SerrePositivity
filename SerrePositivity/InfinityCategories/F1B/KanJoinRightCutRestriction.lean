module

public import SerrePositivity.InfinityCategories.F1B.KanJoinRightShiftPrism
public import SerrePositivity.InfinityCategories.F1B.KanJoinCutRestriction

/-!
概要：元の join の切断より後での先頭・末尾制限。
方針：引き戻した切断を計算し、左右の順序写像を比較する。
規約：空次数を含み、m は元の切断以上。
使われ方：右移動 prism を相対 join へ持ち上げる係数の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：切断以後で先頭を制限すると元の切断が残る。
方針：各頂点の左側への所属による切断の一意性。
規約：m=l も許す。
使われ方：右移動 prism の先頭の係数。 -/
lemma kanJoin_pullCut_prefix_after (r l m : ℕ) (hm : m ≤ r) (hl : l ≤ m) :
    Join.pullCut (Join.prefixIncl r m hm) l = l := by
  apply Join.cut_ext (Join.pullCut_le _ _) hl
  intro i
  rw [Join.lt_pullCut_iff]
  rfl

/-- 概要：切断以後の先頭を除くと、残る頂点は全て右側にある。
方針：末尾の頂点の元の添字は切断以上。
規約：m=r の空区間も許す。
使われ方：右移動 prism の末尾の係数。 -/
lemma kanJoin_pullCut_suffix_after (r l m : ℕ) (hm : m ≤ r) (hl : l ≤ m) :
    Join.pullCut (Join.suffixIncl r m hm) l = 0 := by
  apply Join.cut_ext (Join.pullCut_le _ _) (Nat.zero_le _)
  intro i
  rw [Join.lt_pullCut_iff]
  change m + i.val < l ↔ i.val < 0
  omega

/-- 概要：切断以後で末尾を制限すると右因子の末尾制限の包含になる。
方針：制限後の切断零と順序写像を比較し、空の左因子を消す。
規約：右因子で取り除く頂点数は m−l。
使われ方：右 prism の右係数と元の join の末尾制限の同定。 -/
lemma kanAugJoin_suffix_after {A B : SSet.{u}} (r : ℕ) (s : StableAugJoin A B r)
    (m : ℕ) (hm : m ≤ r) (hl : s.1.val ≤ m) :
    Join.augMap (join A B) (Join.suffixIncl r m hm)
      ((stableAugJoinEquiv A B r).symm s) =
      Join.augHom (joinInr A B) (r - m)
        (cast (congrArg (Join.augObj B) (by omega :
          r - s.1.val - (m - s.1.val) = r - m))
          (Join.augMap B (Join.suffixIncl (r - s.1.val) (m - s.1.val) (by omega)) s.2.2)) := by
  apply (stableAugJoinEquiv A B (r - m)).injective
  rw [stableAugJoinEquiv_naturality, Equiv.apply_symm_apply, stableAugJoinEquiv_inr]
  have hc := kanJoin_pullCut_suffix_after r s.1.val m hm hl
  apply stableAugJoin_hext
  · exact hc
  · exact (stableAugEmpty_heq A hc _).trans (stableAugEmpty_heq A rfl _).symm
  · change HEq (Join.augMap B (Join.rightMap (Join.suffixIncl r m hm) s.1.val) s.2.2)
      (cast _ (Join.augMap B (Join.suffixIncl (r - s.1.val) (m - s.1.val) _) s.2.2))
    refine (stableAugMap_heq B (by rw [hc]; omega) rfl _ _ ?_ _ _ HEq.rfl).trans
      (cast_heq _ _).symm
    intro i j hij
    change m + (Join.pullCut (Join.suffixIncl r m hm) s.1.val + i.val) - s.1.val =
      m - s.1.val + j.val
    omega

/-- 概要：切断以後で先頭を制限した join の切断表示。
方針：左因子はそのまま、右因子は先頭 m−l 頂点への制限と計算する。
規約：左因子の全頂点を保持する。
使われ方：右 prism の逆結合同型で得る左係数の同定。 -/
lemma kanAugJoin_prefix_after {A B : SSet.{u}} (r : ℕ) (s : StableAugJoin A B r)
    (m : ℕ) (hm : m ≤ r) (hl : s.1.val ≤ m) :
    stableAugJoinEquiv A B m
      (Join.augMap (join A B) (Join.prefixIncl r m hm)
        ((stableAugJoinEquiv A B r).symm s)) =
      ⟨⟨s.1.val, by omega⟩, s.2.1,
        Join.augMap B (Join.prefixIncl (r - s.1.val) (m - s.1.val) (by omega)) s.2.2⟩ := by
  rw [stableAugJoinEquiv_naturality, Equiv.apply_symm_apply]
  have hc := kanJoin_pullCut_prefix_after r s.1.val m hm hl
  apply stableAugJoin_hext
  · exact hc
  · have h := stableAugMap_heq A hc rfl
      (Join.leftMap (Join.prefixIncl r m hm) s.1.val) OrderHom.id
      (by intro i j hij; exact hij) s.2.1 s.2.1 HEq.rfl
    rw [Join.augMap_id] at h
    exact h
  · exact stableAugMap_heq B (by change m - Join.pullCut _ s.1.val = m - s.1.val; omega) rfl _ _ (by
      intro i j hij
      change Join.pullCut (Join.prefixIncl r m hm) s.1.val + i.val - s.1.val = j.val
      omega) _ _ HEq.rfl

end SerrePositivity.InfinityCategories
