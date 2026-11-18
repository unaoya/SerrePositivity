module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutGeometry
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GeneralDeletionActive
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionDuplicates

/-!
模型。文献の定義との比較は後で
# 非切断点障害の交換対の係数反対性

概要：Berger–Fresse §2.2.7 の余分な二削除項の実際の整数係数は反対になる。
方針：二位置を順序付け、後の位置が区切りか最終出現かで活動集合の削除公式を使う。
規約：元切断は退化しており、同色三出現も許す。
使われ方：交換で一致する出力テンソルの重み付き相殺。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

private lemma residual_coefficient_ordered {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) (hij : c.deleted < c.defect) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.deleted) c.pivot =
      -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.swap.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.swap.deleted)
        c.swap.pivot) := by
  have hu : u c.deleted = u c.defect := c.defect_spec.2.1.symm
  have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u c.deleted := ⟨c.defect, hij, hu.symm⟩
  have hp := c.swap_pivot
  change c.defect.succAbove c.swap.pivot = c.deleted.succAbove c.pivot at hp
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.deleted) c.pivot =
    -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.defect * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.defect) c.swap.pivot)
  by_cases hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u c.defect
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_caesura u c.deleted c.pivot c.nondegenerate hi,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_caesura u c.defect c.swap.pivot c.swap.nondegenerate hj, hp,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u c.deleted hi,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u c.defect hj]
    have hsign := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionSign_erase_same_color u
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (c.deleted.succAbove c.pivot)) c.deleted c.defect
      (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
      (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
      hij hu (fun k _ => c.same_color_gap k)
    rcases c.defect_spec.2.2 with hs | hs
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_left u _ _ hs.1,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_left u _ _ hs.2] using hsign
    · have hpi : c.deleted.succAbove c.pivot < c.deleted :=
        lt_of_le_of_ne hs.1 (Fin.succAbove_ne c.deleted c.pivot)
      have hpj : c.deleted.succAbove c.pivot < c.defect := lt_trans hpi hij
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_right u _ _ hpi c.pivot_not_caesura,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_right u _ _ hpj c.pivot_not_caesura] at hsign
      simp only [pow_succ, mul_neg_one, neg_mul, neg_neg] at hsign
      simpa only [neg_neg] using congrArg Neg.neg hsign
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_caesura u c.deleted c.pivot c.nondegenerate hi,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_final u c.defect c.deleted c.swap.pivot c.swap.nondegenerate
        hij hu hj c.same_color_gap (by rw [hp]; exact Fin.succAbove_ne _ _), hp,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.deletionCoefficient_final_gap u c.deleted c.defect hij hu hj c.same_color_gap]
    simp only [neg_mul, neg_neg]

/-- 概要：非切断点障害の交換で実際の削除・切断係数は反対（BF §2.2.7）。
方針：二削除位置を順序付けた公式を使い、逆順なら対合を二回適用する。
規約：語の全射性・非退化性を追加で仮定しない。
使われ方：実際の出力テンソルが一致する余分な項を相殺する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap_coefficient {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.deleted) c.pivot =
      -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u c.swap.deleted * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.swap.deleted)
        c.swap.pivot) := by
  rcases lt_or_gt_of_ne c.defect_spec.1 with hji | hij
  · have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residual_coefficient_ordered c.swap hji
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap_swap, neg_neg] using (congrArg Neg.neg h).symm
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residual_coefficient_ordered c hij

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
