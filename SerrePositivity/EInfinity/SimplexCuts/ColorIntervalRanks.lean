module

public import SerrePositivity.EInfinity.SimplexCuts.Faces
public import SerrePositivity.EInfinity.SimplexCuts.IntervalCardinalities

/-!
# 同じ色の頂点列を外側の区間で分けた順位

Berger–Fresse §2.2.3–6、M14 L12a。
元の色別位置集合の順序列挙を、元の水平座標の fiber へ分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の一色の頂点順位のうち、指定した外側区間に属するもの（BF §2.2.6）。 -/
def colorIntervalRanks {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) : Finset (Fin (outputDegree s v a + 1)) :=
  Finset.univ.filter (fun j => s.horizontal
    ((colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a) j) = p)

/-- C353：同じ区間に属する色の順位の個数は、元の区間の頂点数（BF §2.2.6）。 -/
lemma colorIntervalRanks_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    (colorIntervalRanks s v a p).card = (intervalPositions s p).card := by
  let E := (colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a)
  unfold colorIntervalRanks
  refine Finset.card_bij (fun j _ => E j) ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro i _ j _ he
    exact E.injective he
  · intro z hz
    have hzp : s.horizontal z = p := (Finset.mem_filter.mp hz).2
    have hza : z ∈ colorPositions s v.val a := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change v.val (s.horizontal z) = a
      rw [hzp, hp]
    let e := (colorPositions s v.val a).orderIsoOfFin (colorPositions_card_eq s v a)
    let j := e.symm ⟨z, hza⟩
    have hj : E j = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hza⟩)
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
    exact (congrArg s.horizontal hj).trans hzp

/-- C354：指定色を持つ各区間には、その色の順位が存在する（BF §2.2.6）。 -/
lemma colorIntervalRanks_nonempty {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    (colorIntervalRanks s v a p).Nonempty := by
  apply Finset.card_pos.mp
  rw [colorIntervalRanks_card s v a p hp]
  exact Finset.card_pos.mpr (intervalPositions_nonempty s p)

/-- C355：元の外側区間の狭義順序は、同じ色の全順位の狭義順序（BF §2.2.6）。 -/
lemma colorIntervalRanks_ordered {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1)) (hp : p < p')
    (i j : Fin (outputDegree s v a + 1))
    (hi : i ∈ colorIntervalRanks s v a p) (hj : j ∈ colorIntervalRanks s v a p') : i < j := by
  by_contra h
  have hji : j ≤ i := le_of_not_gt h
  have hE := ((colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a)).monotone hji
  have hh := s.horizontal.monotone hE
  rw [(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hi).2] at hh
  exact (not_le_of_gt hp) hh

/-- C356：元の色の全順位は、その色を持つ区間のいずれかへ入る（BF §2.2.6）。 -/
lemma colorIntervalRanks_cover {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s v a + 1)) :
    ∃ p : Fin (m + 1), v.val p = a ∧ j ∈ colorIntervalRanks s v a p := by
  let z := (colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a) j
  have hz : z ∈ colorPositions s v.val a :=
    (colorPositions s v.val a).orderEmbOfFin_mem (colorPositions_card_eq s v a) j
  exact ⟨s.horizontal z, (Finset.mem_filter.mp hz).2,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

end SerrePositivity.EInfinity.SimplexCuts
