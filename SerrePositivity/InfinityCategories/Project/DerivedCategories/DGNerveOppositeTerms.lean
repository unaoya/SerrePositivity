module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeTermSigns
/-!
概要：全実内部点で、符号付き頂点反転が HA 方程式の一項を保存する。
方針：削除項と切断合成項の実比較に、同じ左右濃度の二つの符号式を接続する。
規約：実端点・同じ次数を保つ。使われ方：反対模型の全微分方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGNerveOppositeIndex
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {n : ℕ}
/-- 各実内部点の HA 微分式は、元の同じ反転成分の全体符号倍になる。 -/
lemma op_term (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1))
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).term I a b k hI ha hb hk j hj haj hjb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card • s.term (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
        (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) j.rev
        (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj)
        (Fin.rev_lt_rev.mpr hjb) (Fin.rev_lt_rev.mpr haj) := by
  have hj' : j.rev ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I := by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj
  have hp : ((I.filter (j < ·)).card : ℤ) = ((I.filter (j ≤ ·)).card : ℤ) - 1 := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictRight_card I j hj
    omega
  have hq : (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (j.rev < ·)).card : ℤ) =
      ((I.filter (· ≤ j)).card : ℤ) - 1 := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictLeft_card I j hj
    have he := congrArg Finset.card (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_strictRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) j.rev)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse, Fin.rev_rev] at he
    omega
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_delete I.card (I.filter (· ≤ j)).card (I.filter (j ≤ ·)).card
    (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj).symm
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_split I.card (I.filter (· ≤ j)).card (I.filter (j ≤ ·)).card
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj).symm
  have hdel : ((I.filter (j < ·)).card : ℤ).negOnePow * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.erase j).card =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card * (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (j.rev < ·)).card : ℤ).negOnePow := by
    rw [hp, hq, Finset.card_erase_of_mem hj]
    exact hd.symm
  have hcomp : ((I.filter (j < ·)).card : ℤ).negOnePow *
      (((2 - ((I.filter (· ≤ j)).card : ℤ)) *
        (2 - ((I.filter (j ≤ ·)).card : ℤ))).negOnePow *
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (· ≤ j)).card * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (j ≤ ·)).card) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card * (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (j.rev < ·)).card : ℤ).negOnePow := by
    rw [hp, hq]
    calc
      _ = (((I.filter (j ≤ ·)).card : ℤ) - 1).negOnePow *
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (· ≤ j)).card * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (j ≤ ·)).card *
            ((2 - ((I.filter (· ≤ j)).card : ℤ)) *
              (2 - ((I.filter (j ≤ ·)).card : ℤ))).negOnePow := by ac_rfl
      _ = _ := hc.symm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.term_eq_sub_cutComposite, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op_erasedComponent, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op_cutComposite,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.term_eq_sub_cutComposite]
  simp only [smul_sub, smul_smul]
  rw [hdel, hcomp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
