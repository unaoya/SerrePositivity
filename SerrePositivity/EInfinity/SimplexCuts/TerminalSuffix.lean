module

public import SerrePositivity.EInfinity.SimplexCuts.VertexLists

/-!
# 末尾の色の出現回数

Berger–Fresse §2.2.6–7、M14 L09a R02。
最後の垂直辺の後は、同じ単体の頂点を色の出現回数だけ繰り返す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 最後の垂直辺の後に残る区間番号。 -/
def terminalSuffixIndex {m : ℕ} (p : Fin (m + 1)) (j : Fin (m - p.val + 1)) :
    Fin (m + 1) := ⟨p.val + j.val, by have hj := j.isLt; have hp := p.isLt; omega⟩

/-- L09a C03：末尾の順序添字を元の色のfiberへ戻して数える。 -/
lemma terminalSuffix_card {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (c : Fin r) :
    (Finset.univ.filter (fun j : Fin (m - p.val + 1) =>
      v (terminalSuffixIndex p j) = c)).card = terminalMultiplicity v p c := by
  unfold terminalMultiplicity
  apply Finset.card_bij (fun j _ => terminalSuffixIndex p j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨by change p.val ≤ p.val + j.val; omega, (Finset.mem_filter.mp hj).2⟩⟩
  · intro i _ j _ h
    apply Fin.ext
    have he := congrArg (fun z : Fin (m + 1) => z.val) h
    change p.val + i.val = p.val + j.val at he
    omega
  · intro i hi
    have hip := (Finset.mem_filter.mp hi).2.1
    let j : Fin (m - p.val + 1) :=
      ⟨i.val - p.val, by have hi := i.isLt; have hp := p.isLt; change p.val ≤ i.val at hip; omega⟩
    have he : terminalSuffixIndex p j = i := by
      apply Fin.ext
      change p.val + (i.val - p.val) = i.val
      change p.val ≤ i.val at hip
      omega
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ (Finset.mem_filter.mp hi).2.2⟩, he⟩

/-- R02の証明分割：一定の頂点を持つ色付き列は、選んだ色の数だけその頂点を返す。 -/
lemma selectColor_constant {r N : ℕ} {β : Type*} (c : Fin r) (v : Fin N → Fin r) (b : β) :
    selectColor c (List.ofFn (fun j => (v j, b))) =
      List.replicate (Finset.univ.filter (fun j => v j = c)).card b := by
  rw [List.ofFn_comp' (fun j => j) (fun j => (v j, b))]
  unfold selectColor
  simp only [List.filter_map, List.map_map]
  have hl : ((List.finRange N).filter (fun j => v j == c)).length =
      (Finset.univ.filter (fun j => v j = c)).card := by
    have he := congrArg List.length (sort_filter_univ N (fun j => v j = c))
    simpa only [Finset.length_sort, beq_eq_decide] using he.symm
  change ((List.finRange N).filter (fun j => v j == c)).map (fun _ => b) = _
  rw [List.map_const', hl]

/-- R02の証明分割：末尾は色の出現回数を保って終点を反復する。 -/
lemma selectColor_terminalSuffix {m r : ℕ} {β : Type*} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (c : Fin r) (b : β) :
    selectColor c (List.ofFn (fun j : Fin (m - p.val + 1) =>
      (v (terminalSuffixIndex p j), b))) = List.replicate (terminalMultiplicity v p c) b := by
  rw [selectColor_constant, terminalSuffix_card]

end SerrePositivity.EInfinity.SimplexCuts
