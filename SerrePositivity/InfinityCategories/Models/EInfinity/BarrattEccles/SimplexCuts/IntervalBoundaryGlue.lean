module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerEndpointCoordinates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEdges

/-!
模型。文献の定義との比較は後で
# 同じ切断区間の共有端点と単調性

Berger–Fresse §2.2.3–6、M14 L12a の分割の復元に使う端点の法則。
元の lo・hi を同じ shuffle 経路で評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C348：元の最初の区間は頂点零から始まる（BF §2.2.3）。 -/
lemma lo_zero {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s 0 = 0 :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_eq_of_bound s 0 0 0 s.horizontal_endpoints.1
    (congrArg Fin.val s.vertical_endpoints.1) (fun _ _ => Nat.zero_le _)

/-- C349：元の最後の区間は最後の単体頂点で終わる（BF §2.2.3）。 -/
lemma hi_last {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (Fin.last m) = q :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_bound s (Fin.last m) q (Fin.last (m + q)) s.horizontal_endpoints.2
    (congrArg Fin.val s.vertical_endpoints.2) (fun j _ => Nat.le_of_lt_succ (s.vertical j).isLt)

/-- C350：隣の二つの元の区間は、同じ水平辺の高さを共有する（BF §2.2.3）。 -/
lemma hi_eq_lo_succ {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i.castSucc = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i.succ := by
  obtain ⟨a, h0, h1, hv⟩ := s.horizontal_edge i
  have ha : a ∈ s.val := by
    by_contra ha
    have hs := (s.step_of_notMem a ha).1
    have he := h1.symm.trans (hs.trans h0)
    have he' := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at he'
    omega
  have hhi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i.castSucc = (s.vertical a.castSucc).val := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi
    rw [← h0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.interval_max_before_horizontal s a ha]
  have hlo : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i.succ = (s.vertical a.succ).val := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_eq_of_bound s i.succ _ a.succ h1 rfl
    intro j hj
    have haj : a.succ ≤ j := by
      by_contra hle
      have hja : j ≤ a.castSucc := by
        change j.val ≤ a.val
        have hjlt := lt_of_not_ge hle
        change j.val < a.val + 1 at hjlt
        omega
      have hm := s.horizontal.monotone hja
      rw [hj, h0] at hm
      have hm' := Fin.le_iff_val_le_val.mp hm
      simp only [Fin.val_succ, Fin.val_castSucc] at hm'
      omega
    exact Fin.le_iff_val_le_val.mp (s.vertical.monotone haj)
  exact hhi.trans ((congrArg Fin.val hv).trans hlo.symm)

/-- C351：元の右端点は区間番号に単調（BF §2.2.3）。 -/
lemma hi_monotone {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) : Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_hi s i.succ

/-- C352：元の左端点は区間番号に単調（BF §2.2.3）。 -/
lemma lo_monotone {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) : Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_hi s i.castSucc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
