module

public import SerrePositivity.EInfinity.IntervalCuts.ResidualCutGeometry
public import SerrePositivity.EInfinity.IntervalCuts.GeneralDeletionActive
public import SerrePositivity.EInfinity.IntervalCuts.InversionDuplicates

/-!
# 非切断点障害の交換対の係数反対性

概要：Berger–Fresse §2.2.7 の余分な二削除項の実際の整数係数は反対になる。
方針：二位置を順序付け、後の位置が区切りか最終出現かで活動集合の削除公式を使う。
規約：元切断は退化しており、同色三出現も許す。
使われ方：交換で一致する出力テンソルの重み付き相殺。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

private lemma residual_coefficient_ordered {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : NonpivotResidualCut u) (hij : c.deleted < c.defect) :
    deletionCoefficient u c.deleted * edgeSign (erase u c.deleted) c.pivot =
      -(deletionCoefficient u c.swap.deleted * edgeSign (erase u c.swap.deleted)
        c.swap.pivot) := by
  have hu : u c.deleted = u c.defect := c.defect_spec.2.1.symm
  have hi : Caesura u c.deleted := ⟨c.defect, hij, hu.symm⟩
  have hp := c.swap_pivot
  change c.defect.succAbove c.swap.pivot = c.deleted.succAbove c.pivot at hp
  change deletionCoefficient u c.deleted * edgeSign (erase u c.deleted) c.pivot =
    -(deletionCoefficient u c.defect * edgeSign (erase u c.defect) c.swap.pivot)
  by_cases hj : Caesura u c.defect
  · rw [edgeSign_erase_caesura u c.deleted c.pivot c.nondegenerate hi,
      edgeSign_erase_caesura u c.defect c.swap.pivot c.swap.nondegenerate hj, hp,
      deletionCoefficient_of_caesura u c.deleted hi,
      deletionCoefficient_of_caesura u c.defect hj]
    have hsign := positionInversionSign_erase_same_color u
      (activePositions u (c.deleted.succAbove c.pivot)) c.deleted c.defect
      (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
      (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
      hij hu (fun k _ => c.same_color_gap k)
    rcases c.defect_spec.2.2 with hs | hs
    · simpa only [positionRank_active_left u _ _ hs.1,
        positionRank_active_left u _ _ hs.2] using hsign
    · have hpi : c.deleted.succAbove c.pivot < c.deleted :=
        lt_of_le_of_ne hs.1 (Fin.succAbove_ne c.deleted c.pivot)
      have hpj : c.deleted.succAbove c.pivot < c.defect := lt_trans hpi hij
      rw [positionRank_active_right u _ _ hpi c.pivot_not_caesura,
        positionRank_active_right u _ _ hpj c.pivot_not_caesura] at hsign
      simp only [pow_succ, mul_neg_one, neg_mul, neg_neg] at hsign
      simpa only [neg_neg] using congrArg Neg.neg hsign
  · rw [edgeSign_erase_caesura u c.deleted c.pivot c.nondegenerate hi,
      edgeSign_erase_final u c.defect c.deleted c.swap.pivot c.swap.nondegenerate
        hij hu hj c.same_color_gap (by rw [hp]; exact Fin.succAbove_ne _ _), hp,
      deletionCoefficient_final_gap u c.deleted c.defect hij hu hj c.same_color_gap]
    simp only [neg_mul, neg_neg]

/-- 概要：非切断点障害の交換で実際の削除・切断係数は反対（BF §2.2.7）。
方針：二削除位置を順序付けた公式を使い、逆順なら対合を二回適用する。
規約：語の全射性・非退化性を追加で仮定しない。
使われ方：実際の出力テンソルが一致する余分な項を相殺する。 -/
lemma NonpivotResidualCut.swap_coefficient {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : NonpivotResidualCut u) :
    deletionCoefficient u c.deleted * edgeSign (erase u c.deleted) c.pivot =
      -(deletionCoefficient u c.swap.deleted * edgeSign (erase u c.swap.deleted)
        c.swap.pivot) := by
  rcases lt_or_gt_of_ne c.defect_spec.1 with hji | hij
  · have h := residual_coefficient_ordered c.swap hji
    simpa only [NonpivotResidualCut.swap_swap, neg_neg] using (congrArg Neg.neg h).symm
  · exact residual_coefficient_ordered c hij

end SerrePositivity.EInfinity.IntervalCuts
