module
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeComponents
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeTermSigns
/-!
概要：全実内部点で、符号付き頂点反転が HA 方程式の一項を保存する。
方針：削除項と切断合成項の実比較に、同じ左右濃度の二つの符号式を接続する。
規約：実端点・同じ次数を保つ。使われ方：反対模型の全微分方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerveOppositeData
open CategoryTheory DifferentialGraded DGNerve DGNerveOppositeIndex DGNerveOppositeSigns
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {n : ℕ}
/-- 各実内部点の HA 微分式は、元の同じ反転成分の全体符号倍になる。 -/
lemma op_term (s : SimplexData R D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1))
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (op s).term I a b k hI ha hb hk j hj haj hjb =
      sign I.card • s.term (reverse I) b.rev a.rev k (two_le_card_reverse hI)
        (reverse_min hI hb) (reverse_max hI ha)
        (by simpa only [card_reverse] using hk) j.rev
        (by simpa only [mem_reverse, Fin.rev_rev] using hj)
        (Fin.rev_lt_rev.mpr hjb) (Fin.rev_lt_rev.mpr haj) := by
  have hj' : j.rev ∈ reverse I := by simpa only [mem_reverse, Fin.rev_rev] using hj
  have hp : ((I.filter (j < ·)).card : ℤ) = ((I.filter (j ≤ ·)).card : ℤ) - 1 := by
    have h := strictRight_card I j hj
    omega
  have hq : (((reverse I).filter (j.rev < ·)).card : ℤ) =
      ((I.filter (· ≤ j)).card : ℤ) - 1 := by
    have h := strictLeft_card I j hj
    have he := congrArg Finset.card (reverse_strictRight (reverse I) j.rev)
    simp only [card_reverse, reverse_reverse, Fin.rev_rev] at he
    omega
  have hd := sign_delete I.card (I.filter (· ≤ j)).card (I.filter (j ≤ ·)).card
    (by omega) (Index.split_card hj).symm
  have hc := sign_split I.card (I.filter (· ≤ j)).card (I.filter (j ≤ ·)).card
    (Index.split_card hj).symm
  have hdel : ((I.filter (j < ·)).card : ℤ).negOnePow * sign (I.erase j).card =
      sign I.card * (((reverse I).filter (j.rev < ·)).card : ℤ).negOnePow := by
    rw [hp, hq, Finset.card_erase_of_mem hj]
    exact hd.symm
  have hcomp : ((I.filter (j < ·)).card : ℤ).negOnePow *
      (((2 - ((I.filter (· ≤ j)).card : ℤ)) *
        (2 - ((I.filter (j ≤ ·)).card : ℤ))).negOnePow *
          sign (I.filter (· ≤ j)).card * sign (I.filter (j ≤ ·)).card) =
      sign I.card * (((reverse I).filter (j.rev < ·)).card : ℤ).negOnePow := by
    rw [hp, hq]
    calc
      _ = (((I.filter (j ≤ ·)).card : ℤ) - 1).negOnePow *
          sign (I.filter (· ≤ j)).card * sign (I.filter (j ≤ ·)).card *
            ((2 - ((I.filter (· ≤ j)).card : ℤ)) *
              (2 - ((I.filter (j ≤ ·)).card : ℤ))).negOnePow := by ac_rfl
      _ = _ := hc.symm
  rw [SimplexData.term_eq_sub_cutComposite, op_erasedComponent, op_cutComposite,
    SimplexData.term_eq_sub_cutComposite]
  simp only [smul_sub, smul_smul]
  rw [hdel, hcomp]
end SerrePositivity.InfinityCategories.DGNerveOppositeData
