module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionCoordinates

/-!
# 一点削除の前後の同じ正規化零項

Berger–Fresse §2.2.6、M14 L12a、報告 §334。
元のpairの単射性を、同じ指定削除座標と唯一の色によって両方向へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 唯一の色の水平削除の前後で非退化性は同値（BF §2.2.6）。 -/
lemma nondegenerate_iff_horizontal_deleted_coordinates {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j)
    (hu : ∀ j, v j = v a → j = a) :
    Nondegenerate t (Surjection.erase v a) ↔ Nondegenerate s v := by
  let ρ : Fin (m + q + 1) → Fin (m + 1 + q + 1) :=
    fun j => k.succAbove (Fin.cast (by omega) j)
  have hρ : Function.Injective ρ := (Fin.strictMono_succAbove k).injective.comp
    (Fin.castOrderIso (by omega)).injective
  have he (j : Fin (m + q + 1)) : pair s v (ρ j) = pair t (Surjection.erase v a) j := by
    apply Prod.ext
    · change v (s.horizontal (ρ j)) = v (a.succAbove (t.horizontal j))
      rw [hh]
    · exact hv j
  have hn (j : Fin (m + q + 1)) : pair s v k ≠ pair s v (ρ j) := by
    intro h
    have hc := congrArg Prod.fst h
    change v (s.horizontal k) = v (s.horizontal (ρ j)) at hc
    rw [hk, hh j] at hc
    exact Fin.succAbove_ne a (t.horizontal j) (hu _ hc.symm)
  have cover (j : Fin (m + 1 + q + 1)) (hj : j ≠ k) : ∃ i, ρ i = j := by
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj
    exact ⟨Fin.cast (by omega) i, hi⟩
  constructor
  · intro ht i j hij
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · exact hj.symm
      · obtain ⟨b, rfl⟩ := cover j hj
        exact False.elim (hn b hij)
    · obtain ⟨b, rfl⟩ := cover i hi
      by_cases hj : j = k
      · subst j
        exact False.elim (hn b hij.symm)
      · obtain ⟨c, rfl⟩ := cover j hj
        exact congrArg ρ (ht ((he b).symm.trans (hij.trans (he c))))
  · intro hs i j hij
    exact hρ (hs ((he i).trans (hij.trans (he j).symm)))

end SerrePositivity.EInfinity.SimplexCuts
