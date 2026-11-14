module

public import SerrePositivity.EInfinity.SimplexCuts.WeightedVertexInversions
public import SerrePositivity.EInfinity.SimplexCuts.BoundaryVertexLists
public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundaryTerms

/-!
# 実際のBF境界符号を活動頂点で読む

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の出力境界符号の面番号・次数・逆転指数を同じ活動頂点の有限集合へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts (positionInversionCount)

/-- C108：指定頂点より前の同色は全て活動的なので、面番号は同じ先行数。 -/
lemma vertexRank_eq_active_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
    vertexRank s v (label s v k) k =
      ((activeVertexPositions s v).filter (fun j => j < k ∧ label s v j = label s v k)).card := by
  rw [vertexRank_eq_card]
  congr 1
  ext j
  simp only [colorPositions, activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hj⟩
    exact ⟨⟨k, hj, hc.symm⟩, hj, hc⟩
  · rintro ⟨_, hj, hc⟩
    exact ⟨hc, hj⟩

/-- C109：小さい色の出力次数の和は、その色の活動頂点の全数。 -/
lemma prefixOutputDegree_eq_active_card {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
    (∑ b ∈ Finset.univ.filter (fun b : Fin r => b < c), outputDegree s v b) =
      ((activeVertexPositions s v.val).filter (fun j => label s v.val j < c)).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (activeVertexPositions s v.val)
    (Finset.univ.filter (fun b : Fin r => b < c)) (label s v.val)
  simp_rw [active_color_card] at h
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- 同じ出力境界符号を、削除する経路の頂点で指定する。 -/
def outputBoundarySignAt {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (k : Fin (m + q + 1)) : ℤ :=
  outputBoundarySign s v ((colorPositionEquiv s v).symm k).1
    ((colorPositionEquiv s v).symm k).2

/-- C110：元の出力境界符号の全指数を活動頂点の数で計算する。 -/
lemma outputBoundarySignAt_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
    outputBoundarySignAt s v k = cutSign s v.val * (-1 : ℤ) ^
      (((activeVertexPositions s v.val).filter (fun j => label s v.val j < label s v.val k)).card +
      ((activeVertexPositions s v.val).filter (fun j => j < k ∧
        label s v.val j = label s v.val k)).card) := by
  unfold outputBoundarySignAt outputBoundarySign
  rw [← vertexRank_symm_colorPositionEquiv s v k, colorPositionEquiv_symm_color,
    prefixOutputDegree_eq_active_card, vertexRank_eq_active_card]

/-- C111：活動頂点を削除するBF境界符号は、残る逆転符号と元位置順の面符号で計算できる。 -/
lemma outputBoundarySignAt_of_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ activeVertexPositions s v.val) :
    outputBoundarySignAt s v k =
      (-1 : ℤ) ^ positionExponent s v.val *
        (-1 : ℤ) ^
          positionInversionCount (label s v.val) ((activeVertexPositions s v.val).erase k) *
        (-1 : ℤ) ^ ((activeVertexPositions s v.val).filter (fun j => j < k)).card := by
  rw [outputBoundarySignAt_active]
  unfold cutSign
  rw [permutationExponent_eq_active_inversions, ← pow_add]
  have he : (positionInversionCount (label s v.val) (activeVertexPositions s v.val) +
      positionExponent s v.val) +
      (((activeVertexPositions s v.val).filter (fun j => label s v.val j < label s v.val k)).card +
      ((activeVertexPositions s v.val).filter (fun j => j < k ∧
        label s v.val j = label s v.val k)).card) =
      positionExponent s v.val +
      (positionInversionCount (label s v.val) (activeVertexPositions s v.val) +
      ((activeVertexPositions s v.val).filter (fun j => label s v.val j < label s v.val k)).card +
      ((activeVertexPositions s v.val).filter (fun j => j < k ∧
        label s v.val j = label s v.val k)).card) := by
    omega
  rw [he, pow_add, colorSorting_boundary_sign (label s v.val) (activeVertexPositions s v.val) k hk]
  simp only [mul_assoc]

end SerrePositivity.EInfinity.SimplexCuts
