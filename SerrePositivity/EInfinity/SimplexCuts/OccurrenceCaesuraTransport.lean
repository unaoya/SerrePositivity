module

public import SerrePositivity.EInfinity.Surjection.Caesuras
public import Mathlib.Order.Hom.Basic

/-!
# 同じ全出現位置の順序同値による区切りの移送

Berger–Fresse §1.2.2・§2.2.4、M14 L12a のC452の符号の法則。
区切りは元の位置より後の同じラベルの存在だけで比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 全出現位置の同じ順序同値は、元の区切りを保つ（BF §1.2.2）。 -/
lemma caesura_iff_of_occurrenceOrderIso {r r' l l' : ℕ}
    (v : Fin l → Fin r) (w : Fin l' → Fin r') (a : Fin r) (b : Fin r')
    (e : ↥(Surjection.occurrences v a) ≃o ↥(Surjection.occurrences w b))
    (p : ↥(Surjection.occurrences v a)) :
    Surjection.Caesura w (e p).val ↔ Surjection.Caesura v p.val := by
  have hp : v p.val = a := (Finset.mem_filter.mp p.property).2
  have hep : w (e p).val = b := (Finset.mem_filter.mp (e p).property).2
  constructor
  · rintro ⟨j, hj, hjv⟩
    let j' : ↥(Surjection.occurrences w b) :=
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjv.trans hep⟩⟩
    let i := e.symm j'
    have he : e i = j' := e.apply_symm_apply j'
    refine ⟨i.val, ?_, (Finset.mem_filter.mp i.property).2.trans hp.symm⟩
    have hi : p < i := e.lt_iff_lt.mp (by rw [he]; exact hj)
    exact hi
  · rintro ⟨i, hi, hiv⟩
    let i' : ↥(Surjection.occurrences v a) :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv.trans hp⟩⟩
    refine ⟨(e i').val, ?_, (Finset.mem_filter.mp (e i').property).2.trans hep.symm⟩
    exact e.strictMono (show p < i' from hi)

end SerrePositivity.EInfinity.SimplexCuts
