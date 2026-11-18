module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualIndices

/-!
模型。文献の定義との比較は後で
# 切断点障害削除と隙間の隣接退化切断の有限同値

概要：Berger–Fresse §2.2.7 の全切断点障害項を左右の隙間に隣接する退化切断で添字付ける。
方針：非退化隙間の反対側の同色位置の一意性と削除の順序単射を使う。
規約：元の非零辺切断の存在を仮定しない。
使われ方：実際の全削除和の有限添字替え。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {n l : ℕ} {u : Fin (l + 1) → Fin n}

/-- 概要：非退化な直前隙間を持つ退化辺切断の有限型（BF §2.2.7）。
方針：元切断点に二つの判定の証明を付ける。
規約：左の同色削除項に対応する。
使われ方：共通係数が負となる隙間和。 -/
abbrev BeforeCut (u : Fin (l + 1) → Fin n) :=
  {p : Fin (l + 1) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc ∧ ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p}

/-- 概要：非退化な直後隙間を持つ退化辺切断の有限型（BF §2.2.7）。
方針：元切断点に二つの判定の証明を付ける。
規約：右の同色削除項に対応する。
使われ方：共通係数が正となる隙間和。 -/
abbrev AfterCut (u : Fin (l + 1) → Fin n) :=
  {p : Fin (l + 1) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ ∧ ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p}

/-- 概要：左削除を元切断点と直前隙間の対へ送る（BF §2.2.7）。
方針：削除後の非零性から隙間の非退化性を得る。
規約：元の辺切断は退化する。
使われ方：左の全削除和の添字替えの順写像。 -/
def beforeCut (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.Before u) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.BeforeCut u :=
  ⟨c.val.deleted.succAbove c.val.pivot,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_before_of_erase_pivot u c.val.deleted c.val.pivot c.val.nondegenerate c.property
      c.val.same_color, c.val.original_degenerate⟩

/-- 概要：右削除を元切断点と直後隙間の対へ送る（BF §2.2.7）。
方針：削除後の非零性から隙間の非退化性を得る。
規約：元の辺切断は退化する。
使われ方：右の全削除和の添字替えの順写像。 -/
def afterCut (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.After u) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.AfterCut u :=
  ⟨c.val.deleted.succAbove c.val.pivot,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_after_of_erase_pivot u c.val.deleted c.val.pivot c.val.nondegenerate c.property
      c.val.same_color, c.val.original_degenerate⟩

/-- 概要：左削除から隙間に隣接する退化切断への写像の単射性（BF §2.2.7）。
方針：隙間側の一意な同色相手と削除順序単射を使う。
規約：証明付き有限添字で比較する。
使われ方：実際の全削除和の有限同値を構成する。 -/
lemma beforeCut_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.beforeCut (u := u)) := by
  intro c d he
  have hp := congrArg Subtype.val he
  change c.val.deleted.succAbove c.val.pivot = d.val.deleted.succAbove d.val.pivot at hp
  have hd := d.property
  rw [← hp] at hd
  have hi : c.val.deleted = d.val.deleted :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.beforeCut c).property.1.1 _ _ c.property hd
      ((c.val.same_color.trans (congrArg u hp)).trans d.val.same_color.symm)
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.ext hi
  apply (Fin.succAbove_right_injective (p := d.val.deleted))
  simpa only [hi] using hp

/-- 概要：右削除から隙間に隣接する退化切断への写像の単射性（BF §2.2.7）。
方針：隙間側の一意な同色相手と削除順序単射を使う。
規約：証明付き有限添字で比較する。
使われ方：実際の全削除和の有限同値を構成する。 -/
lemma afterCut_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.afterCut (u := u)) := by
  intro c d he
  have hp := congrArg Subtype.val he
  change c.val.deleted.succAbove c.val.pivot = d.val.deleted.succAbove d.val.pivot at hp
  have hd := d.property
  rw [← hp] at hd
  have hi : c.val.deleted = d.val.deleted :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.afterCut c).property.1.2 _ _ (Nat.add_one_le_of_lt c.property)
      (Nat.add_one_le_of_lt hd)
      ((c.val.same_color.trans (congrArg u hp)).trans d.val.same_color.symm)
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.ext hi
  apply (Fin.succAbove_right_injective (p := d.val.deleted))
  simpa only [hi] using hp

/-- 概要：左削除から隙間に隣接する退化切断への写像の全射性（BF §2.2.7）。
方針：隙間側の一意な同色相手と削除順序単射を使う。
規約：証明付き有限添字で比較する。
使われ方：実際の全削除和の有限同値を構成する。 -/
lemma beforeCut_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.beforeCut (u := u)) := by
  intro p
  obtain ⟨i, hi, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_before_defect_existsUnique u p.val p.property.1 p.property.2
  obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq (ne_of_gt hi.1)
  have hg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).castSucc := by
    rw [hq]
    exact p.property.1
  have hip : i < i.succAbove q := by rw [hq]; exact hi.1
  have hu : u i = u (i.succAbove q) := by rw [hq]; exact hi.2
  let c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u :=
    ⟨i, q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate_of_gap_before u i q hg hip hu, hu⟩
  refine ⟨⟨c, hip⟩, ?_⟩
  exact Subtype.ext hq

/-- 概要：右削除から隙間に隣接する退化切断への写像の全射性（BF §2.2.7）。
方針：隙間側の一意な同色相手と削除順序単射を使う。
規約：証明付き有限添字で比較する。
使われ方：実際の全削除和の有限同値を構成する。 -/
lemma afterCut_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.afterCut (u := u)) := by
  intro p
  obtain ⟨i, hi, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_after_defect_existsUnique u p.val p.property.1 p.property.2
  obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq (ne_of_lt hi.1)
  have hg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).succ := by
    rw [hq]
    exact p.property.1
  have hip : i.succAbove q < i := by rw [hq]; exact hi.1
  have hu : u i = u (i.succAbove q) := by rw [hq]; exact hi.2
  let c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u :=
    ⟨i, q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate_of_gap_after u i q hg hip hu, hu⟩
  refine ⟨⟨c, hip⟩, ?_⟩
  exact Subtype.ext hq

/-- 概要：左の切断点障害削除項と直前隙間が非退化な退化切断の有限同値（BF §2.2.7）。
方針：元切断点への写像の単射性と全射性を使う。
規約：実際の削除位置は同色相手の一意性から復元される。
使われ方：左の全削除和を負の隙間値の和へ移す。 -/
def beforeEquiv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.Before u ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.BeforeCut u :=
  Equiv.ofBijective _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.beforeCut ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.beforeCut_injective, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.beforeCut_surjective⟩

/-- 概要：右の切断点障害削除項と直後隙間が非退化な退化切断の有限同値（BF §2.2.7）。
方針：元切断点への写像の単射性と全射性を使う。
規約：実際の削除位置は同色相手の一意性から復元される。
使われ方：右の全削除和を正の隙間値の和へ移す。 -/
def afterEquiv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.After u ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.AfterCut u :=
  Equiv.ofBijective _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.afterCut ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.afterCut_injective, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.afterCut_surjective⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut
