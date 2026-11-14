module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedCompleteTop
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearPullback

/-! # pinched 削除右辺の全面による最上位評価

概要：線形データの最上位削除右辺を、各面の最上位成分の符号付き和として書く。
方針：余面の全体集合の像は一点削除集合である。
規約：整数次数を明示する。使われ方：正規化した境界の指定原始元による充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 余面を引き戻した線形データの最上位成分は、指定頂点を消した元の成分。 -/
lemma pinchedLinearData_top_face {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1))
    (j : Fin (n + 2)) (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom f).component Finset.univ k
      Finset.univ_nonempty hk =
        f.component (Finset.univ.erase j) k (by apply Finset.card_pos.mp; simp)
          (by simpa using hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  have hi : (Finset.univ : Finset (Fin (n + 1))).image j.succAboveOrderEmb.toOrderHom =
      Finset.univ.erase j := by
    change Finset.image j.succAbove Finset.univ = _
    simpa only [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase] using
      Fin.image_succAbove_univ j
  simp only [hi]

/-- 全体の削除右辺は各実面の最上位成分の符号付き和。 -/
lemma pinchedLinearData_rhs_full_faces {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1))
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    f.rhs Finset.univ k hk =
      ∑ j : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign Finset.univ j •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom f).component Finset.univ (k + 1)
          Finset.univ_nonempty (by simp at hk ⊢; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rhs_eq_deleteSum]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum
  apply Finset.sum_congr rfl
  intro j _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign Finset.univ j • f.componentOrZero (Finset.univ.erase j) (k + 1) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq f (Finset.univ.erase j) (k + 1)
    (by apply Finset.card_pos.mp; simp) (by simp at hk ⊢; omega), pinchedLinearData_top_face]

/-- 最上位次数は一つ次元を上げると一つ下がる。 -/
lemma pinchedTopDegree_succ (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) + 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree]

/-- 全体集合の零頂点を消す係数は次元に二を加えた負一冪。 -/
lemma pinchedDeletionSign_zero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign (Finset.univ : Finset (Fin (n + 2))) 0 = ((n : ℤ) + 2).negOnePow := by
  have hf : (Finset.univ : Finset (Fin (n + 2))).filter (0 < ·) = Finset.univ.erase 0 := by
    ext a
    simp [Fin.pos_iff_ne_zero]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign, hf]
  congr 1

end SerrePositivity.InfinityCategories.Project.DerivedCategories
