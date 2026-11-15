module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveNestedCuts

/-!
# 同じ語長の移送による元の出現位置

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の内側射影の証明分割。
元の出現位置を、positiveWordが用いる同じ長さで読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C410：同じ語長の移送では、同じ番号の文字は変わらない（BF §1.2.1）。 -/
lemma word_eq_mp_value {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (i : Fin l') (j : Fin l) (hij : i.val = j.val) :
    (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val i = v.val j := by
  subst l'
  exact congrArg v.val (Fin.ext hij)

/-- 元の指定色の出現位置を、切断の区間数と同じ長さで読む（BF §1.2.4）。 -/
def positiveOccurrencePosition {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (j : Fin (Surjection.occurrenceCount u.val k)) : Fin (m + d + 1) :=
  ⟨(Surjection.occurrenceAt u.val k j).val, by
    have h := (Surjection.occurrenceAt u.val k j).isLt
    omega⟩

/-- C411：同じ出現位置の文字は元の指定色（BF §1.2.4）。 -/
lemma positiveOccurrencePosition_value {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (j : Fin (Surjection.occurrenceCount u.val k)) :
    (positiveWord u).val (positiveOccurrencePosition u k j) = k := by
  unfold positiveWord
  exact (word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u
    (positiveOccurrencePosition u k j) (Surjection.occurrenceAt u.val k j) rfl).trans
      (Surjection.occurrenceAt_value u.val k j)

/-- C412：同じ語長で読んでも元の出現位置の狭義順序は変わらない（BF §1.2.4）。 -/
lemma positiveOccurrencePosition_strictMono {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) :
    StrictMono (positiveOccurrencePosition u k) := by
  intro i j hij
  exact Surjection.occurrenceAt_strictMono u.val k hij

end SerrePositivity.EInfinity.SimplexCuts
