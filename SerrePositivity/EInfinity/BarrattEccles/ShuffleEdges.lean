module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePaths

/-!
# shuffle 経路が通る水平辺と垂直辺

概要：Berger–Fresse §1.1.3 の格子経路が各座標の隣接値を結ぶ辺を持つことを証明する。
方針：指定座標の上端へ最初に到達する頂点を取り、その直前の頂点を調べる。
規約：水平辺では垂直座標が固定され、垂直辺では水平座標が固定される。
使われ方：退化した入力を含む shuffle 項が退化することを証明する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：全射な有限順序の写像は各隣接値を結ぶ単位ステップを持つ（Berger–Fresse §1.1.3）。
方針：上端の値になる最初の頂点を取り、増分の上界から直前の値を決める。
規約：端点 0 を保ち、一つのステップの増加が高々 1 であると仮定する。
使われ方：shuffle の各座標の辺を持ち上げる。 -/
lemma fin_unit_step_hits {N P : ℕ} (f : Fin (N + 1) → Fin (P + 1))
    (hzero : f 0 = 0) (hf : Function.Surjective f)
    (hstep : ∀ i : Fin N, (f i.succ).val ≤ (f i.castSucc).val + 1)
    (j : Fin P) : ∃ i : Fin N, f i.castSucc = j.castSucc ∧ f i.succ = j.succ := by
  let S := Finset.univ.filter (fun k => j.succ ≤ f k)
  obtain ⟨a, ha⟩ := hf j.succ
  have hS : S.Nonempty := ⟨a, by simp [S, ha]⟩
  let k := S.min' hS
  have hk : j.succ ≤ f k := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hk₀ : k ≠ 0 := by
    intro hk₀
    rw [hk₀, hzero] at hk
    have hh := Fin.le_iff_val_le_val.mp hk
    simp only [Fin.val_succ, Fin.val_zero] at hh
    omega
  obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero hk₀
  have hprev : ¬ j.succ ≤ f i.castSucc := by
    intro h
    have hm := S.min'_le i.castSucc (by simp [S, h])
    change k ≤ i.castSucc at hm
    rw [hi] at hm
    exact (not_le_of_gt i.castSucc_lt_succ) hm
  rw [hi] at hk
  have hs := hstep i
  refine ⟨i, Fin.ext ?_, Fin.ext ?_⟩
  all_goals
    change j.val + 1 ≤ (f i.succ).val at hk
    change ¬ j.val + 1 ≤ (f i.castSucc).val at hprev
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

/-- 概要：shuffle 経路は各水平辺を一度ずつ通る（Berger–Fresse §1.1.3）。
方針：水平座標の指定辺を持ち上げ、座標和の公式で垂直座標の固定を示す。
規約：この補題では必要な辺の存在と両端の座標を述べる。
使われ方：第一の置換列の重複頂点を合成列の重複頂点へ移す。 -/
lemma ShufflePath.horizontal_edge {p q : ℕ} (s : ShufflePath p q) (j : Fin p) :
    ∃ i : Fin (p + q), s.horizontal i.castSucc = j.castSucc ∧
      s.horizontal i.succ = j.succ ∧ s.vertical i.castSucc = s.vertical i.succ := by
  have hstep (i : Fin (p + q)) :
      (s.horizontal i.succ).val ≤ (s.horizontal i.castSucc).val + 1 := by
    rcases s.unit_step i with h | h
    · omega
    · have hx := congrArg Fin.val h.1
      omega
  obtain ⟨i, h₀, h₁⟩ := fin_unit_step_hits s.horizontal s.horizontal_endpoints.1
    s.horizontal_surjective hstep j
  refine ⟨i, h₀, h₁, Fin.ext ?_⟩
  have hs₀ := s.coordinate_sum i.castSucc
  have hs₁ := s.coordinate_sum i.succ
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  simp only [Fin.val_castSucc, Fin.val_succ] at hs₀ hs₁
  omega

/-- 概要：shuffle 経路は各垂直辺を一度ずつ通る（Berger–Fresse §1.1.3）。
方針：垂直座標の指定辺を持ち上げ、座標和の公式で水平座標の固定を示す。
規約：この補題では必要な辺の存在と両端の座標を述べる。
使われ方：第二の置換列の重複頂点を合成列の重複頂点へ移す。 -/
lemma ShufflePath.vertical_edge {p q : ℕ} (s : ShufflePath p q) (j : Fin q) :
    ∃ i : Fin (p + q), s.vertical i.castSucc = j.castSucc ∧
      s.vertical i.succ = j.succ ∧ s.horizontal i.castSucc = s.horizontal i.succ := by
  have hstep (i : Fin (p + q)) :
      (s.vertical i.succ).val ≤ (s.vertical i.castSucc).val + 1 := by
    rcases s.unit_step i with h | h
    · have hy := congrArg Fin.val h.2
      omega
    · omega
  obtain ⟨i, h₀, h₁⟩ := fin_unit_step_hits s.vertical s.vertical_endpoints.1
    s.vertical_surjective hstep j
  refine ⟨i, h₀, h₁, Fin.ext ?_⟩
  have hs₀ := s.coordinate_sum i.castSucc
  have hs₁ := s.coordinate_sum i.succ
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  simp only [Fin.val_castSucc, Fin.val_succ] at hs₀ hs₁
  omega

end SerrePositivity.EInfinity.BarrattEccles
