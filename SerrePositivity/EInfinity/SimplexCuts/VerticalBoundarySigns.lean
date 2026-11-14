module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalDeletionCoefficients
public import SerrePositivity.EInfinity.SimplexCuts.VerticalDeletionExponents
public import SerrePositivity.EInfinity.SimplexCuts.ErasedColorSignComparisons

/-!
# 垂直境界の実符号と入力面の交代符号

Berger–Fresse §1.2.3・§2.2.4・§2.2.7、M14 L09a。
同じ語の区切り数、位置指数、展開語の削除係数を合わせ、指定された入力面の符号へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C234：接頭順位と末尾側の区切り数の和は、元の語の次数。 -/
lemma caesuraRank_add_tail_card {m r : ℕ} (v : Surjection.Word r (m + 1))
    (a : Fin (m + 1)) :
    Surjection.caesuraRank v.val a +
      ((caesuraPositions v.val).filter (fun i => a ≤ i)).card = m + 1 - r := by
  have hcard : (caesuraPositions v.val).card = m + 1 - r := by
    simpa only [Fintype.card_subtype, caesuraPositions] using v.card_caesuras
  have h := Finset.card_filter_add_card_filter_not (s := caesuraPositions v.val) (fun i => i < a)
  simpa only [caesuraRank_eq_filter_card, not_lt, hcard] using h

/-- C235：位置指数と垂直の削除係数の指数の和を、語の次数と入力頂点へ戻す。 -/
lemma positionExponent_plus_vertical_rank {m q r : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    positionExponent s v.val +
        ((s.vertical k).val + Surjection.caesuraRank v.val (s.horizontal k)) =
      (m + 1 - r + (s.vertical k).val) + positionExponent t v.val := by
  have hp := positionExponent_vertical_deleted_coordinates s t v.val k hk hh hv
  have hc := caesuraRank_add_tail_card v (s.horizontal k)
  omega

/-- C236：垂直の実境界符号は、語の次数と入力面番号の交代符号を掛けた小さい切断の符号。 -/
lemma outputBoundarySignAt_vertical_of_coordinates {m q r : ℕ} (s : Cut m (q + 1)) (t : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) :
    outputBoundarySignAt s v k =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) * cutSign t v.val := by
  have hlen : m + (q + 1) = m + q + 1 := by omega
  have hperm := erasedColorSign_eq_permutationSign s v.val k t v.val hlen (by
    intro j
    have hc : Fin.cast hlen j = j := Fin.ext rfl
    change v.val (s.horizontal (k.succAbove j)) = v.val (t.horizontal (Fin.cast hlen j))
    rw [hc]
    exact congrArg v.val (hh j))
  rw [outputBoundarySignAt_erase s v k (outputDegree_pos_vertical s v k hk), hperm,
    deletionCoefficient_vertical s v.val k hk]
  have regroup (a b c : ℤ) : a * b * c = (a * c) * b := by ac_rfl
  rw [regroup, ← pow_add, positionExponent_plus_vertical_rank s t v k hk hh hv]
  simp only [cutSign, pow_add]
  ac_rfl

end SerrePositivity.EInfinity.SimplexCuts
