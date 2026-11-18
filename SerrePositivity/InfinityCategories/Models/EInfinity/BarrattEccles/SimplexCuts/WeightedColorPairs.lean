module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.AdjacentCutSigns

/-!
模型。文献の定義との比較は後で
# 重複する色を許した二色位置対と隣接交換の符号

Berger–Fresse §2.2.4、M14 L11 の証明分割。
元の二色位置対を、二つの色の fiber の積を位置順に並べたものとして数える。
色の単射性は仮定せず、一般の単体の出力次数を保持する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open scoped _root_.symmDiff

/-- C318：元の二色位置対の個数は、両色の fiber の濃度の積（BF §2.2.4）。 -/
lemma card_colorCrossPairs_weighted {n l : ℕ} (v : Fin l → Fin n)
    (s : Finset (Fin l)) (a b : Fin n) (hab : a ≠ b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs v s a b).card =
      (s.filter (fun i => v i = a)).card * (s.filter (fun i => v i = b)).card := by
  let F : Fin l × Fin l → Fin l × Fin l := fun p => if p.1 < p.2 then p else p.swap
  have recover (p : Fin l × Fin l)
      (hp : p ∈ (s.filter (fun i => v i = a)) ×ˢ (s.filter (fun i => v i = b))) :
      (if v (F p).1 = a then F p else (F p).swap) = p := by
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hpa := (Finset.mem_filter.mp hp1).2
    have hpb := (Finset.mem_filter.mp hp2).2
    by_cases hlt : p.1 < p.2
    · simp only [F, hlt, ↓reduceIte, hpa]
    · simp only [F, hlt, ↓reduceIte, Prod.fst_swap, hpb,
        show b ≠ a from hab.symm, Prod.swap_swap]
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun p _ => F p) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    rcases Finset.mem_filter.mp hp1 with ⟨hp1, hpa⟩
    rcases Finset.mem_filter.mp hp2 with ⟨hp2, hpb⟩
    have hne : p.1 ≠ p.2 := by
      intro he
      exact hab (hpa.symm.trans ((congrArg v he).trans hpb))
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs v s a b _).mpr
    by_cases hlt : p.1 < p.2
    · simpa only [F, hlt, ↓reduceIte] using
        (show p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 ∧
          ((v p.1 = a ∧ v p.2 = b) ∨ (v p.1 = b ∧ v p.2 = a)) from
            ⟨hp1, hp2, hlt, Or.inl ⟨hpa, hpb⟩⟩)
    · have hgt : p.2 < p.1 := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      simpa only [F, hlt, ↓reduceIte, Prod.fst_swap, Prod.snd_swap] using
        (show p.2 ∈ s ∧ p.1 ∈ s ∧ p.2 < p.1 ∧
          ((v p.2 = a ∧ v p.1 = b) ∨ (v p.2 = b ∧ v p.1 = a)) from
            ⟨hp2, hp1, hgt, Or.inr ⟨hpb, hpa⟩⟩)
  · intro p hp q hq he
    have hh := congrArg (fun z : Fin l × Fin l => if v z.1 = a then z else z.swap) he
    rw [recover p hp, recover q hq] at hh
    exact hh
  · intro p hp
    rcases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs v s a b p).mp hp with
      ⟨hp1, hp2, hlt, hcolors⟩
    rcases hcolors with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩
    · refine ⟨p, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp1, hpa⟩,
        Finset.mem_filter.mpr ⟨hp2, hpb⟩⟩, ?_⟩
      simp only [F, hlt, ↓reduceIte]
    · refine ⟨p.swap, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp2, hpa⟩,
        Finset.mem_filter.mpr ⟨hp1, hpb⟩⟩, ?_⟩
      simp only [F, Prod.fst_swap, Prod.snd_swap, not_lt_of_gt hlt, ↓reduceIte,
        Prod.swap_swap]

/-- C319：隣接交換の逆転符号は、重複を保った二色の出現数の積で変わる（BF §2.2.4）。 -/
lemma positionInversionSign_adjacent_weighted {n l : ℕ} (a : Fin n)
    (v : Fin l → Fin (n + 1)) (s : Finset (Fin l)) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (_root_.SerrePositivity.Coxeter.adjacentTransposition a ∘ v) s =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v s *
        (-1 : ℤ) ^ ((s.filter (fun i => v i = a.castSucc)).card *
          (s.filter (fun i => v i = a.succ)).card) := by
  have hab : a.castSucc ≠ a.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.neg_one_pow_card_symmDiff
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions (_root_.SerrePositivity.Coxeter.adjacentTransposition a ∘ v) s)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions v s)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions_symmDiff_adjacent] at h
  change (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions (_root_.SerrePositivity.Coxeter.adjacentTransposition a ∘ v) s).card =
    (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions v s).card *
      (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs v s a.castSucc a.succ).card at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.card_positionInversions,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.card_colorCrossPairs_weighted v s a.castSucc a.succ hab] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
