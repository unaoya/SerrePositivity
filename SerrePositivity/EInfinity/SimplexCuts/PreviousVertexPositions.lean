module

public import SerrePositivity.EInfinity.SimplexCuts.ActiveBoundarySigns
public import SerrePositivity.EInfinity.Surjection.DeletionSigns

/-!
# 直前の同色の頂点と面番号

Berger–Fresse §2.2.7、M14 L09a。
既存のpreviousOccurrencesの最大を取り、同じ色の連続する二つの面番号を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 既存の同色の先行位置集合の最大。 -/
def previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : Fin N :=
  (Surjection.previousOccurrences v k).max' h

lemma previousVertex_mem {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
    previousVertex v k h ∈ Surjection.previousOccurrences v k :=
  (Surjection.previousOccurrences v k).max'_mem h

lemma previousVertex_lt {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : previousVertex v k h < k :=
  (Finset.mem_filter.mp (previousVertex_mem v k h)).2.1

lemma previousVertex_value {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) : v (previousVertex v k h) = v k :=
  (Finset.mem_filter.mp (previousVertex_mem v k h)).2.2

/-- C112：直前の同色位置を除くと、その位置より前の同色位置だけが残る。 -/
lemma previousOccurrences_erase_previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
    (Surjection.previousOccurrences v k).erase (previousVertex v k h) =
      Surjection.previousOccurrences v (previousVertex v k h) := by
  ext j
  simp only [Finset.mem_erase, Surjection.previousOccurrences, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hjk, hv⟩
    have hm : j ∈ Surjection.previousOccurrences v k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk, hv⟩
    exact ⟨lt_of_le_of_ne ((Surjection.previousOccurrences v k).le_max' j hm) hne,
      hv.trans (previousVertex_value v k h).symm⟩
  · rintro ⟨hjp, hv⟩
    exact ⟨ne_of_lt hjp, lt_trans hjp (previousVertex_lt v k h),
      hv.trans (previousVertex_value v k h)⟩

/-- C113：直前の同色位置の先行数は、指定位置の先行数より一つ小さい。 -/
lemma previousOccurrences_card_previousVertex {N r : ℕ} (v : Fin N → Fin r) (k : Fin N)
    (h : (Surjection.previousOccurrences v k).Nonempty) :
    (Surjection.previousOccurrences v (previousVertex v k h)).card + 1 =
      (Surjection.previousOccurrences v k).card := by
  rw [← previousOccurrences_erase_previousVertex, Finset.card_erase_of_mem
    (previousVertex_mem v k h)]
  have hp := Finset.card_pos.mpr h
  omega

/-- C114：直前の同色頂点は、その後に指定頂点を持つので活動的。 -/
lemma previousVertex_active {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (h : (Surjection.previousOccurrences (label s v) k).Nonempty) :
    previousVertex (label s v) k h ∈ activeVertexPositions s v :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, previousVertex_lt _ _ h,
    (previousVertex_value _ _ h).symm⟩

lemma vertexRank_eq_previousOccurrences_card {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
    vertexRank s v (label s v k) k = (Surjection.previousOccurrences (label s v) k).card := by
  rw [vertexRank_eq_card]
  congr 1
  ext j
  simp only [colorPositions, Surjection.previousOccurrences, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact and_comm

/-- C115：同色の直前頂点との、実際の面番号の差は一。 -/
lemma vertexRank_previousVertex {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (h : (Surjection.previousOccurrences (label s v) k).Nonempty) :
    vertexRank s v (label s v k) k =
      vertexRank s v (label s v (previousVertex (label s v) k h))
        (previousVertex (label s v) k h) + 1 := by
  rw [vertexRank_eq_previousOccurrences_card, vertexRank_eq_previousOccurrences_card]
  exact (previousOccurrences_card_previousVertex _ _ h).symm

end SerrePositivity.EInfinity.SimplexCuts
