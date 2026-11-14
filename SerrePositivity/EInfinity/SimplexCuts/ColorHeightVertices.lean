module

public import SerrePositivity.EInfinity.SimplexCuts.ColorHeightRanks
public import Mathlib.Order.Interval.Finset.Nat

/-!
# 同じ色別順位で読む元の頂点の高さ

Berger–Fresse §2.2.3–6、M14 L12a の内側射影の照合。
元の色別位置列の狭義単調性と区間全体の幅から、途中の高さも厳密に特定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C403：有限の狭義単調列の値の増分は添字の増分以上（BF §2.2.6 の列挙の補助）。 -/
lemma finite_strictMono_distance {N : ℕ} (f : Fin N → ℕ) (hf : StrictMono f)
    (i j : Fin N) (hij : i ≤ j) : j.val - i.val ≤ f j - f i := by
  have hc : (Finset.Icc i j).card ≤ (Finset.Icc (f i) (f j)).card :=
    Finset.card_le_card_of_injOn f (fun k hk => by
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨hf.monotone hl, hf.monotone hr⟩) hf.injective.injOn
  rw [Fin.card_Icc, Nat.card_Icc] at hc
  have hm := hf.monotone hij
  have hv : i.val ≤ j.val := hij
  omega

/-- C404：元の区間内の順位の差は、その同じ頂点の高さの差（BF §2.2.6）。 -/
lemma vertices_on_colorIntervalRanks {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    (vertices s v a j).val = lo s p + (j.val - (colorIntervalFirst s v a p hp).val) := by
  let E := (colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a)
  let first := colorIntervalFirst s v a p hp
  let last := colorIntervalLast s v a p hp
  have hfirst : s.horizontal (E first) = p :=
    (Finset.mem_filter.mp ((colorIntervalRanks s v a p).min'_mem
      (colorIntervalRanks_nonempty s v a p hp))).2
  have hlast : s.horizontal (E last) = p :=
    (Finset.mem_filter.mp ((colorIntervalRanks s v a p).max'_mem
      (colorIntervalRanks_nonempty s v a p hp))).2
  have hjp : s.horizontal (E j) = p := (Finset.mem_filter.mp hj).2
  have hfj : first ≤ j := (colorIntervalRanks s v a p).min'_le j hj
  have hjl : j ≤ last := (colorIntervalRanks s v a p).le_max' j hj
  have he1 : (E first).val ≤ (E j).val := E.monotone hfj
  have he2 : (E j).val ≤ (E last).val := E.monotone hjl
  have hd1 := finite_strictMono_distance (fun x => (E x).val)
    (Fin.val_strictMono.comp E.strictMono) first j hfj
  have hd2 := finite_strictMono_distance (fun x => (E x).val)
    (Fin.val_strictMono.comp E.strictMono) j last hjl
  have hc1 := s.coordinate_sum (E first)
  have hc2 := s.coordinate_sum (E j)
  have hc3 := s.coordinate_sum (E last)
  rw [hfirst] at hc1
  rw [hjp] at hc2
  rw [hlast] at hc3
  have hl := lo_le_vertical s p (E first) hfirst
  have hr := vertical_le_hi s p (E last) hlast
  have hw := colorIntervalRank_width s v a p hp
  change last.val - first.val = hi s p - lo s p at hw
  have hlohi := lo_le_hi s p
  have hvfj : first.val ≤ j.val := hfj
  have hvjl : j.val ≤ last.val := hjl
  change (s.vertical (E j)).val = lo s p + (j.val - first.val)
  dsimp only [first, last, E] at *
  omega

/-- C405：指定順位は元のverticesによって同じ高さを読む（BF §2.2.6）。 -/
lemma vertices_colorHeightRank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p) :
    (vertices s v a (colorHeightRank s v a p hp h hl hr)).val = h := by
  rw [vertices_on_colorIntervalRanks s v a p hp _ (colorHeightRank_mem s v a p hp h hl hr)]
  change lo s p +
    ((colorIntervalFirst s v a p hp).val + (h - lo s p) -
      (colorIntervalFirst s v a p hp).val) = h
  omega

end SerrePositivity.EInfinity.SimplexCuts
