module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalCardinalities
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorCaesuraCounts

/-!
模型。文献の定義との比較は後で
# 出力次数と区間の符号次数の和

Berger–Fresse §2.2.3–4、M14 L09a。
各色の頂点を区間のfiberに分け、最後以外の出現の一をcaesuraとして数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C96：一つの色の頂点数は、その色の各区間の頂点数の和。 -/
lemma colorPositions_card_by_intervals {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (c : Fin r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v c).card =
      ∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v c, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).card := by
  have ht := Finset.card_eq_sum_card_fiberwise
    (f := s.horizontal) (s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v c) (t := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v c)
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
  refine ht.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ext j
  have hv : v i = c := (Finset.mem_filter.mp hi).2
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hj⟩
    exact hj
  · intro hj
    refine ⟨?_, hj⟩
    change v (s.horizontal j) = c
    rw [hj]
    exact hv

/-- C97：各色の出力次数は、その色の区間の符号次数を足した値。 -/
lemma outputDegree_eq_sum_intervalLength {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v c = ∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s v.val i := by
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_by_intervals s v.val c
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_card] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hc
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_caesura_occurrences_add_one v c
  have hw : (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s v.val i) =
      (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val c, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i)) +
      (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val c, if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val i then 1 else 0) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength, Finset.sum_add_distrib]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
