module

public import SerrePositivity.EInfinity.SimplexCuts.TerminalExtension

/-!
# 最後の垂直辺とその前の切断

Berger–Fresse §2.2.6–7、M14 L09a R01の順向きの構成。
水平辺集合の補集合の最大元を取り、そこより前を圧縮する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

lemma verticalPositions_nonempty {m q : ℕ} (s : Cut m (q + 1)) : s.valᶜ.Nonempty := by
  apply Finset.card_pos.mp
  rw [s.compl_card]
  omega

def lastVertical {m q : ℕ} (s : Cut m (q + 1)) : Fin (m + (q + 1)) :=
  s.valᶜ.max' (verticalPositions_nonempty s)

lemma lastVertical_mem {m q : ℕ} (s : Cut m (q + 1)) : lastVertical s ∈ s.valᶜ :=
  s.valᶜ.max'_mem (verticalPositions_nonempty s)

lemma le_lastVertical {m q : ℕ} (s : Cut m (q + 1)) (i : Fin (m + (q + 1)))
    (hi : i ∈ s.valᶜ) : i ≤ lastVertical s := s.valᶜ.le_max' i hi

/-- R01の証明分割：最後の垂直辺より前にq個の垂直辺がある。 -/
lemma lastVertical_lower_card {m q : ℕ} (s : Cut m (q + 1)) :
    (lowerPart s.valᶜ (lastVertical s)).card = q := by
  have h := card_lowerPart_of_max s.valᶜ (lastVertical s) (lastVertical_mem s)
    (fun i hi => le_lastVertical s i hi)
  rw [s.compl_card] at h
  omega

lemma q_le_lastVertical {m q : ℕ} (s : Cut m (q + 1)) : q ≤ (lastVertical s).val := by
  have h := (lowerPart s.valᶜ (lastVertical s)).card_le_univ
  simp only [Fintype.card_fin, lastVertical_lower_card] at h
  exact h

/-- 最後の垂直辺の属する区間。 -/
def lastVerticalColor {m q : ℕ} (s : Cut m (q + 1)) : Fin (m + 1) :=
  ⟨(lastVertical s).val - q, by have h := (lastVertical s).isLt; omega⟩

lemma lastVerticalColor_add {m q : ℕ} (s : Cut m (q + 1)) :
    (lastVerticalColor s).val + q = (lastVertical s).val := by
  have h := q_le_lastVertical s
  change (lastVertical s).val - q + q = (lastVertical s).val
  omega

lemma lastVertical_horizontal_card {m q : ℕ} (s : Cut m (q + 1)) :
    (lowerPart s.val (lastVertical s)).card = (lastVerticalColor s).val := by
  have h₁ := lastVertical_lower_card s
  rw [lowerPart_compl] at h₁
  have h₂ := Finset.card_compl (lowerPart s.val (lastVertical s))
  have h₃ := (lowerPart s.val (lastVertical s)).card_le_univ
  simp only [Fintype.card_fin] at h₂ h₃
  change (lowerPart s.val (lastVertical s)).card = (lastVertical s).val - q
  omega

/-- 最後の垂直辺の前の水平辺だけを取った切断。 -/
def terminalPrefix {m q : ℕ} (s : Cut m (q + 1)) : Cut (lastVerticalColor s).val q := by
  let p := lastVerticalColor s
  let a := lastVertical s
  let f := terminalPrefixEmbedding m q p
  let t := Finset.univ.filter (fun i => f i ∈ s.val)
  have ha : a.val = p.val + q := (lastVerticalColor_add s).symm
  have hc : t.card = (lowerPart s.val a).card := by
    apply Finset.card_bij (fun i _ => Fin.cast ha.symm i)
    · intro i hi
      apply (mem_lowerPart s.val a _).mpr
      have he : lowerEmbedding a (Fin.cast ha.symm i) = f i := by apply Fin.ext; rfl
      rw [he]
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      apply Fin.ext
      exact congrArg (fun z : Fin a.val => z.val) hij
    · intro j hj
      refine ⟨Fin.cast ha j, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have he : f (Fin.cast ha j) = lowerEmbedding a j := by apply Fin.ext; rfl
        rw [he]
        exact (mem_lowerPart s.val a j).mp hj
      · apply Fin.ext
        rfl
  exact ⟨t, hc.trans (lastVertical_horizontal_card s)⟩

lemma terminalPrefix_mem {m q : ℕ} (s : Cut m (q + 1))
    (i : Fin ((lastVerticalColor s).val + q)) :
    i ∈ (terminalPrefix s).val ↔ terminalPrefixEmbedding m q (lastVerticalColor s) i ∈ s.val := by
  change i ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- R01の証明分割：逆構成の最後の垂直辺は、指定して足した辺。 -/
lemma lastVertical_terminalExtend (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q) :
    lastVertical (terminalExtend m q p s) = terminalEdge m q p := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_compl.mpr (terminalEdge_not_mem m q p s)
  · intro j hj
    by_contra h
    have hj' : terminalEdge m q p < j := lt_of_not_ge h
    exact (Finset.mem_compl.mp hj) (terminalExtend_above_mem m q p s j hj')

end SerrePositivity.EInfinity.SimplexCuts
