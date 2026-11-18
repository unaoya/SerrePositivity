module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalData

/-!
模型。文献の定義との比較は後で
# 最後の垂直辺による切断の分解

Berger–Fresse §2.2.6–7、M14 L09a R01。
末尾の水平辺を取り除く操作と、それを戻す操作が互いに逆である。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- R01の証明分割：最後の垂直辺の前後を合わせると元の切断に戻る。 -/
lemma terminalExtend_terminalPrefix {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefix s) = s := by
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalEdge m q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s := by
    apply Fin.ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor_add s
  apply Subtype.ext
  ext j
  by_cases hj : j < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s
  · let i : Fin ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s).val + q) :=
      ⟨j.val, by
        have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor_add s
        change j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val at hj
        omega⟩
    have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixEmbedding m q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s) i = j := Fin.ext rfl
    rw [← hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_mem_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefix_mem]
  · by_cases hje : j = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s
    · subst j
      rw [← he]
      exact iff_of_false (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalEdge_not_mem _ _ _ _) (by
        rw [he]
        exact Finset.mem_compl.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_mem s))
    · have hlt : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s < j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hje)
      have hmem : j ∈ s.val := by
        by_contra h
        exact (not_le_of_gt hlt) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.le_lastVertical s j (Finset.mem_compl.mpr h))
      exact iff_of_true (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_above_mem _ _ _ _ j (he ▸ hlt)) hmem

/-- R01の証明分割：復元した切断から接頭部も区間番号も一意に読める。 -/
lemma terminalExtend_injective (m q : ℕ) : Function.Injective
    (fun t : Σ p : Fin (m + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q t.1 t.2) := by
  rintro ⟨p, s⟩ ⟨p', s'⟩ h
  have he := congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_terminalExtend, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_terminalExtend] at he
  have hp : p = p' := by
    apply Fin.ext
    have hv := congrArg (fun z : Fin (m + (q + 1)) => z.val) he
    change p.val + q = p'.val + q at hv
    omega
  cases hp
  have hs : s = s' := by
    apply Subtype.ext
    ext i
    have hm := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1) =>
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixEmbedding m q p i ∈ t.val) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_mem_prefix] using (Iff.of_eq hm)
  cases hs
  rfl

/-- R01。最後の垂直辺の区間と、その前の切断による分解。 -/
def cutLastVerticalEquiv (m q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1) ≃ Σ p : Fin (m + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q :=
  (Equiv.ofBijective
    (fun t : Σ p : Fin (m + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q t.1 t.2)
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_injective m q,
      fun s => ⟨⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefix s⟩, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_terminalPrefix s⟩⟩).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
