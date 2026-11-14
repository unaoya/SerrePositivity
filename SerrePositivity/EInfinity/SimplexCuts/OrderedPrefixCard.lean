module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-!
# 同じ昇順列挙の一位置より前の濃度

Berger–Fresse §2.2.3–6、M14 L12a の経路復元の証明分割。
元のorderEmbOfFinを使い、その第i位置より前の元を同じFinの初期区間で数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C377：元の昇順列挙の第i位置より前の濃度はi（BF §2.2.3）。 -/
lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] (s : Finset α)
    {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter (fun x => x < s.orderEmbOfFin h i)).card = i.val := by
  let E := s.orderEmbOfFin h
  have hc : (Finset.Iio i).card = (s.filter (fun x => x < E i)).card := by
    refine Finset.card_bij (fun j _ => E j) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_filter.mpr ⟨s.orderEmbOfFin_mem h j,
        E.strictMono (Finset.mem_Iio.mp hj)⟩
    · intro j _ k _ he
      exact E.injective he
    · intro x hx
      let e := s.orderIsoOfFin h
      let j := e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩
      have hj : E j = x := congrArg Subtype.val (e.apply_symm_apply _)
      have hji : j < i := by
        apply E.lt_iff_lt.mp
        rw [hj]
        exact (Finset.mem_filter.mp hx).2
      exact ⟨j, Finset.mem_Iio.mpr hji, hj⟩
  exact hc.symm.trans (Fin.card_Iio i)

end SerrePositivity.EInfinity.SimplexCuts
