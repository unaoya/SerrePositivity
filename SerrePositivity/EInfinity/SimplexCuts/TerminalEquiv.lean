module

public import SerrePositivity.EInfinity.SimplexCuts.TerminalData

/-!
# 最後の垂直辺による切断の分解

Berger–Fresse §2.2.6–7、M14 L09a R01。
末尾の水平辺を取り除く操作と、それを戻す操作が互いに逆である。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- R01の証明分割：最後の垂直辺の前後を合わせると元の切断に戻る。 -/
lemma terminalExtend_terminalPrefix {m q : ℕ} (s : Cut m (q + 1)) :
    terminalExtend m q (lastVerticalColor s) (terminalPrefix s) = s := by
  have he : terminalEdge m q (lastVerticalColor s) = lastVertical s := by
    apply Fin.ext
    exact lastVerticalColor_add s
  apply Subtype.ext
  ext j
  by_cases hj : j < lastVertical s
  · let i : Fin ((lastVerticalColor s).val + q) :=
      ⟨j.val, by
        have h := lastVerticalColor_add s
        change j.val < (lastVertical s).val at hj
        omega⟩
    have hi : terminalPrefixEmbedding m q (lastVerticalColor s) i = j := Fin.ext rfl
    rw [← hi, terminalExtend_mem_prefix, terminalPrefix_mem]
  · by_cases hje : j = lastVertical s
    · subst j
      rw [← he]
      exact iff_of_false (terminalEdge_not_mem _ _ _ _) (by
        rw [he]
        exact Finset.mem_compl.mp (lastVertical_mem s))
    · have hlt : lastVertical s < j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hje)
      have hmem : j ∈ s.val := by
        by_contra h
        exact (not_le_of_gt hlt) (le_lastVertical s j (Finset.mem_compl.mpr h))
      exact iff_of_true (terminalExtend_above_mem _ _ _ _ j (he ▸ hlt)) hmem

/-- R01の証明分割：復元した切断から接頭部も区間番号も一意に読める。 -/
lemma terminalExtend_injective (m q : ℕ) : Function.Injective
    (fun t : Σ p : Fin (m + 1), Cut p.val q => terminalExtend m q t.1 t.2) := by
  rintro ⟨p, s⟩ ⟨p', s'⟩ h
  have he := congrArg lastVertical h
  rw [lastVertical_terminalExtend, lastVertical_terminalExtend] at he
  have hp : p = p' := by
    apply Fin.ext
    have hv := congrArg (fun z : Fin (m + (q + 1)) => z.val) he
    change p.val + q = p'.val + q at hv
    omega
  cases hp
  have hs : s = s' := by
    apply Subtype.ext
    ext i
    have hm := congrArg (fun t : Cut m (q + 1) =>
      terminalPrefixEmbedding m q p i ∈ t.val) h
    simpa only [terminalExtend_mem_prefix] using (Iff.of_eq hm)
  cases hs
  rfl

/-- R01。最後の垂直辺の区間と、その前の切断による分解。 -/
def cutLastVerticalEquiv (m q : ℕ) :
    Cut m (q + 1) ≃ Σ p : Fin (m + 1), Cut p.val q :=
  (Equiv.ofBijective
    (fun t : Σ p : Fin (m + 1), Cut p.val q => terminalExtend m q t.1 t.2)
    ⟨terminalExtend_injective m q,
      fun s => ⟨⟨lastVerticalColor s, terminalPrefix s⟩, terminalExtend_terminalPrefix s⟩⟩).symm

end SerrePositivity.EInfinity.SimplexCuts
