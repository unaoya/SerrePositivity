module

public import SerrePositivity.EInfinity.Surjection.CompositionSigns

/-!
# 語長の等式による同じ区切りと順位の移送

Berger–Fresse §1.2.5・§2.2.6、M14 L12a の C452。
報告 §289 の同じ有限位置・同じ順位の証明分割。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ値の位置で、語長の等式は区切りを保つ（BF §1.2.5）。 -/
lemma caesura_word_eq_mp {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (p : Fin l') (q : Fin l) (hpq : p.val = q.val) :
    Surjection.Caesura (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val p ↔
      Surjection.Caesura v.val q := by
  subst l'
  have he : p = q := Fin.ext hpq
  subst p
  rfl

/-- 同じ値の位置で、語長の等式は区切り順位を保つ（BF §1.2.5）。 -/
lemma caesuraRank_word_eq_mp {r l l' : ℕ} (h : l = l') (v : Surjection.Word r l)
    (p : Fin l') (q : Fin l) (hpq : p.val = q.val) :
    Surjection.caesuraRank (Eq.mp (congrArg (fun L => Surjection.Word r L) h) v).val p =
      Surjection.caesuraRank v.val q := by
  subst l'
  have he : p = q := Fin.ext hpq
  subst p
  rfl

end SerrePositivity.EInfinity.SimplexCuts
