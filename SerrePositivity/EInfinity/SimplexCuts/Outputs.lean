module

public import SerrePositivity.EInfinity.SimplexCuts.Expanded
public import SerrePositivity.EInfinity.Surjection.Words
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 一般の区間切断の色と出力次数

Berger–Fresse §2.2.1–3。全射語の各色は切断後も出現する。
各色の展開位置を数え、切断の全出力次数を計算する（5a-5a L01・L02）。
退化した切断も含め、正規化による消滅より前の頂点列を保持する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

lemma colorPositions_nonempty {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) :
    (colorPositions s u.val a).Nonempty := by
  obtain ⟨j, hj⟩ := u.surjective a
  obtain ⟨i, hi⟩ := s.horizontal_surjective j
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact (congrArg u.val hi).trans hj

/-- 色ごとの頂点列の次数。重複した頂点も正規化の前には残す（BF §2.2.3）。 -/
def outputDegree {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1))
    (a : Fin r) : ℕ := (colorPositions s u.val a).card - 1

/-- L02 の証明の分割：各色の頂点数はその次数に一を足した値。 -/
lemma colorPositions_card_eq {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) :
    (colorPositions s u.val a).card = outputDegree s u a + 1 := by
  have h := Finset.card_pos.mpr (colorPositions_nonempty s u a)
  unfold outputDegree
  omega

/-- L02 の証明の分割：色の fiber は全展開位置を分割する。 -/
lemma colorPositions_card_sum {m q r : ℕ} (s : Cut m q)
    (u : Fin (m + 1) → Fin r) :
    ∑ a : Fin r, (colorPositions s u a).card = m + q + 1 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := label s u) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin, colorPositions] using h.symm

/-- 全射語の切断の全出力次数。退化性を仮定しない（BF §2.2.3）。 -/
lemma outputDegree_sum {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) :
    ∑ a : Fin r, outputDegree s u a = m + q + 1 - r := by
  have h := colorPositions_card_sum s u.val
  simp_rw [colorPositions_card_eq s u] at h
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

end SerrePositivity.EInfinity.SimplexCuts
