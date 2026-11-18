module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalExtension

/-!
模型。文献の定義との比較は後で
# 最後の垂直辺とその前の切断

Berger–Fresse §2.2.6–7、M14 L09a R01の順向きの構成。
水平辺集合の補集合の最大元を取り、そこより前を圧縮する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

lemma verticalPositions_nonempty {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) : s.valᶜ.Nonempty := by
  apply Finset.card_pos.mp
  rw [s.compl_card]
  omega

def lastVertical {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) : Fin (m + (q + 1)) :=
  s.valᶜ.max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalPositions_nonempty s)

lemma lastVertical_mem {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s ∈ s.valᶜ :=
  s.valᶜ.max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalPositions_nonempty s)

lemma le_lastVertical {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) (i : Fin (m + (q + 1)))
    (hi : i ∈ s.valᶜ) : i ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s := s.valᶜ.le_max' i hi

/-- R01の証明分割：最後の垂直辺より前にq個の垂直辺がある。 -/
lemma lastVertical_lower_card {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.valᶜ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s)).card = q := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.card_lowerPart_of_max s.valᶜ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_mem s)
    (fun i hi => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.le_lastVertical s i hi)
  rw [s.compl_card] at h
  omega

lemma q_le_lastVertical {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) : q ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val := by
  have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.valᶜ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s)).card_le_univ
  simp only [Fintype.card_fin, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_lower_card] at h
  exact h

/-- 最後の垂直辺の属する区間。 -/
def lastVerticalColor {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) : Fin (m + 1) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val - q, by have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).isLt; omega⟩

lemma lastVerticalColor_add {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s).val + q = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.q_le_lastVertical s
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val - q + q = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val
  omega

lemma lastVertical_horizontal_card {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s)).card = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s).val := by
  have h₁ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_lower_card s
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart_compl] at h₁
  have h₂ := Finset.card_compl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s))
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s)).card_le_univ
  simp only [Fintype.card_fin] at h₂ h₃
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s)).card = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s).val - q
  omega

/-- 最後の垂直辺の前の水平辺だけを取った切断。 -/
def terminalPrefix {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s).val q := by
  let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s
  let a := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical s
  let f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixEmbedding m q p
  let t := Finset.univ.filter (fun i => f i ∈ s.val)
  have ha : a.val = p.val + q := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor_add s).symm
  have hc : t.card = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerPart s.val a).card := by
    apply Finset.card_bij (fun i _ => Fin.cast ha.symm i)
    · intro i hi
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mem_lowerPart s.val a _).mpr
      have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a (Fin.cast ha.symm i) = f i := by apply Fin.ext; rfl
      rw [he]
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      apply Fin.ext
      exact congrArg (fun z : Fin a.val => z.val) hij
    · intro j hj
      refine ⟨Fin.cast ha j, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have he : f (Fin.cast ha j) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lowerEmbedding a j := by apply Fin.ext; rfl
        rw [he]
        exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mem_lowerPart s.val a j).mp hj
      · apply Fin.ext
        rfl
  exact ⟨t, hc.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_horizontal_card s)⟩

lemma terminalPrefix_mem {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s).val + q)) :
    i ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefix s).val ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixEmbedding m q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVerticalColor s) i ∈ s.val := by
  change i ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- R01の証明分割：逆構成の最後の垂直辺は、指定して足した辺。 -/
lemma lastVertical_terminalExtend (m q : ℕ) (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalEdge m q p := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_compl.mpr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalEdge_not_mem m q p s)
  · intro j hj
    by_contra h
    have hj' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalEdge m q p < j := lt_of_not_ge h
    exact (Finset.mem_compl.mp hj) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_above_mem m q p s j hj')

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
