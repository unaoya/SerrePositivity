module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionCoefficients
public import SerrePositivity.EInfinity.SimplexCuts.ErasedColorSignComparisons
public import SerrePositivity.EInfinity.SimplexCuts.SingletonFiberSteps

/-!
# 水平境界の実際の出力符号

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
同じ削除色列の逆転符号と、元の語へ戻した削除係数を合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C183：指定座標で対応する水平境界の実符号は、元の語の削除係数と小さい切断の符号。 -/
lemma outputBoundarySignAt_horizontal_of_coordinates {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < outputDegree s v (label s v.val k))
    (hh : ∀ i, hi t i = hi s (a.succAbove i))
    (hw : w.val = Surjection.erase v.val a)
    (he : ∀ i, Surjection.erase (label s v.val) k i =
      label t w.val (Fin.cast (by omega : m + 1 + q = m + q + 1) i)) :
    outputBoundarySignAt s v k = Surjection.deletionCoefficient v.val a * cutSign t w.val := by
  rw [outputBoundarySignAt_erase _ _ _ hd,
    erasedColorSign_eq_permutationSign s v.val k t w.val (by omega) he]
  have hc := signedDeletionCoefficient_horizontal s t v a k hk hsingle hd hh
  rw [← hw] at hc
  have rearrange (P E D : ℤ) : P * E * D = E * (P * D) := by ac_rfl
  rw [rearrange, hc, cutSign, pow_add]
  ac_rfl

/-- C184：内部の水平境界の実符号の比較。削除語が有効な場合。 -/
lemma outputBoundarySignAt_horizontalDeletion {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (a b : Fin (m + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ)) :
    outputBoundarySignAt s v a.succ =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) *
        cutSign ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w.val := by
  have hH : HorizontalVertex s a.succ := by
    constructor
    · intro c hc
      have heq : c = a := Fin.ext (by
        have h := congrArg (fun z : Fin (m + 1 + q + 1) => z.val) hc
        change c.val + 1 = a.val + 1 at h
        omega)
      exact heq ▸ ha
    · intro c hc
      have heq : c = b := Fin.ext (by
        have h := congrArg (fun z : Fin (m + 1 + q + 1) => z.val) hc
        change c.val = a.val + 1 at h
        omega)
      exact heq ▸ hb
  refine outputBoundarySignAt_horizontal_of_coordinates s _ v w (s.horizontal a.succ)
    a.succ rfl ((horizontal_fiber_singleton_iff s a.succ).mpr hH) hd
    (hi_horizontalDeletion s a b hab ha hb) hw ?_
  intro i
  rw [hw]
  change v.val (s.horizontal (a.succ.succAbove i)) =
    v.val ((s.horizontal a.succ).succAbove
      (((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal (Fin.cast _ i)))
  exact congrArg v.val (BarrattEccles.horizontalDeletion_horizontal s a b hab ha hb i)

end SerrePositivity.EInfinity.SimplexCuts
