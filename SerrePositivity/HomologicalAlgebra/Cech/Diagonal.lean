module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Ring.Parity

/-!
概要：第一象限の増大二重複体の行と列の完全性を比較する。
方針：全複体のサイクルを有限な対角線で取り、完全な行を順に使って境界で消す。
規約：零番の行・列も増大項から始まる。可換な微分には列に行次数の符号を入れる。
使われ方：二重 Čech 複体による完全性の比較。
-/

@[expose] public section

universe u

namespace SerrePositivity.Cech

section

variable (X : ℕ → ℕ → Type u) [∀ i j, AddCommGroup (X i j)]
variable (h : ∀ i j, X i j →+ X (i + 1) j) (v : ∀ i j, X i j →+ X i (j + 1))

private abbrev Grid := ∀ i j, X i j

private def horizontal (x : Grid X) (i j : ℕ) : X i j :=
  match i with
  | 0 => 0
  | k + 1 => h k j (x k j)

private def vertical (x : Grid X) (i j : ℕ) : X i j :=
  match j with
  | 0 => 0
  | k + 1 => v i k (x i k)

private def totalD : Grid X →+ Grid X where
  toFun x i j := horizontal X h x i j + vertical X v x i j
  map_zero' := by
    funext i j
    cases i <;> cases j <;> simp [horizontal, vertical]
  map_add' x y := by
    funext i j
    cases i <;> cases j <;> simp [horizontal, vertical, add_add_add_comm]

private theorem totalD_sq
    (hh : ∀ i j x, h (i + 1) j (h i j x) = 0)
    (vv : ∀ i j x, v i (j + 1) (v i j x) = 0)
    (hv : ∀ i j x, h i (j + 1) (v i j x) + v (i + 1) j (h i j x) = 0)
    (x : Grid X) : totalD X h v (totalD X h v x) = 0 := by
  funext i j
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
    simp [totalD, horizontal, vertical, hh, vv, hv]

private def On (n : ℤ) (x : Grid X) : Prop :=
  ∀ i j : ℕ, (i : ℤ) + j ≠ n → x i j = 0

private theorem On.add {n : ℤ} {x y : Grid X} (hx : On X n x) (hy : On X n y) :
    On X n (x + y) :=
  fun i j hne => by simp [hx i j hne, hy i j hne]

private theorem On.sub {n : ℤ} {x y : Grid X} (hx : On X n x) (hy : On X n y) :
    On X n (x - y) :=
  fun i j hne => by simp [hx i j hne, hy i j hne]

private theorem On.totalD {n : ℤ} {x : Grid X} (hx : On X n x) :
    On X (n + 1) (totalD X h v x) := by
  intro i j hn
  have hi (i' : ℕ) (e : i = i' + 1) : horizontal X h x i j = 0 := by
    subst i
    exact (congrArg (h i' j) (hx i' j (by omega))).trans (map_zero _)
  have hj (j' : ℕ) (e : j = j' + 1) : vertical X v x i j = 0 := by
    subst j
    exact (congrArg (v i j') (hx i j' (by omega))).trans (map_zero _)
  change horizontal X h x i j + vertical X v x i j = 0
  have h₁ : horizontal X h x i j = 0 := by
    cases i with
    | zero => rfl
    | succ i => exact hi i rfl
  have h₂ : vertical X v x i j = 0 := by
    cases j with
    | zero => rfl
    | succ j => exact hj j rfl
  rw [h₁, h₂, add_zero]

private def cell (i j : ℕ) (a : X i j) : Grid X :=
  Function.update 0 i (Function.update 0 j a)

@[simp]
private theorem cell_at (i j : ℕ) (a : X i j) : cell X i j a i j = a := by simp [cell]

private theorem cell_of_col_ne {i j k l : ℕ} (a : X i j) (hne : l ≠ j) :
    cell X i j a k l = 0 := by
  by_cases hi : k = i
  · subst k
    simp [cell, Function.update_of_ne hne]
  · simp [cell, Function.update_of_ne hi]

private theorem cell_on (i j : ℕ) (a : X i j) : On X ((i : ℤ) + j) (cell X i j a) := by
  intro k l hne
  by_cases hi : k = i
  · subst k
    exact cell_of_col_ne X a (by intro hj; subst l; exact hne rfl)
  · simp [cell, Function.update_of_ne hi]

/-- 指定した行の増大項を含む完全性。 -/
def RowExact (j : ℕ) : Prop :=
  (∀ x, h 0 j x = 0 → x = 0) ∧ ∀ i x, h (i + 1) j x = 0 → ∃ y, h i j y = x

/-- 指定した列の増大項を含む完全性。 -/
def ColExact (i : ℕ) : Prop :=
  (∀ x, v i 0 x = 0 → x = 0) ∧ ∀ j x, v i (j + 1) x = 0 → ∃ y, v i j y = x

private def TotalExact : Prop :=
  ∀ (n : ℕ) x, On X n x → totalD X h v x = 0 →
    ∃ y, On X ((n : ℤ) - 1) y ∧ totalD X h v y = x

private theorem totalD_below {c : ℕ} {x : Grid X} (hx : ∀ i j, j < c → x i j = 0)
    (i j : ℕ) (hj : j < c) : totalD X h v x i j = 0 := by
  change horizontal X h x i j + vertical X v x i j = 0
  have hi : horizontal X h x i j = 0 := by
    cases i with
    | zero => rfl
    | succ i => simp [horizontal, hx i j hj]
  have hv : vertical X v x i j = 0 := by
    cases j with
    | zero => rfl
    | succ j => simp [vertical, hx i j (Nat.lt_of_succ_lt hj)]
  rw [hi, hv, add_zero]

private theorem clearColumns
    (hh : ∀ i j x, h (i + 1) j (h i j x) = 0)
    (vv : ∀ i j x, v i (j + 1) (v i j x) = 0)
    (hv : ∀ i j x, h i (j + 1) (v i j x) + v (i + 1) j (h i j x) = 0)
    (c n : ℕ) (hex : ∀ j, c ≤ j → RowExact X h j)
    (x : Grid X) (hx : On X n x) (hcyc : totalD X h v x = 0)
    (hbelow : ∀ i j, j < c → x i j = 0) :
    ∃ y, On X ((n : ℤ) - 1) y ∧ (∀ i j, j < c → y i j = 0) ∧ totalD X h v y = x := by
  have step (m : ℕ) : ∃ y, On X ((n : ℤ) - 1) y ∧
      (∀ i j, j < c → y i j = 0) ∧
      ∀ i j, j < m → (x - totalD X h v y) i j = 0 := by
    induction m with
    | zero => exact ⟨0, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ hlt => by omega⟩
    | succ m ih =>
      obtain ⟨y, hy, hyc, hlow⟩ := ih
      let z := x - totalD X h v y
      have hz : On X n z := hx.sub X (by
        have hd := On.totalD X h v hy
        simpa only [show (n : ℤ) - 1 + 1 = n by omega] using hd)
      have hzd : totalD X h v z = 0 := by
        rw [map_sub, hcyc, totalD_sq X h v hh vv hv, sub_zero]
      have hzm (i : ℕ) : h i m (z i m) = 0 := by
        have he := congrFun (congrFun hzd (i + 1)) m
        cases m with
        | zero => simpa [totalD, horizontal, vertical] using he
        | succ m =>
          have hzprev : z (i + 1) m = 0 := hlow _ _ (Nat.lt_succ_self _)
          simpa [totalD, horizontal, vertical, hzprev] using he
      by_cases hcm : c ≤ m
      · by_cases hmn : m ≤ n
        · let i := n - m
          have hin : (i : ℤ) + m = n := by dsimp [i]; omega
          cases hi : i with
          | zero =>
            have hm0 : z 0 m = 0 := (hex m hcm).1 _ (hzm 0)
            refine ⟨y, hy, hyc, fun a j hj => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · exact hlow a j hj
            · cases a with
              | zero => exact hm0
              | succ a => exact hz _ _ (by omega)
          | succ k =>
            obtain ⟨b, hb⟩ := (hex m hcm).2 k (z (k + 1) m) (hzm (k + 1))
            let t := cell X k m b
            have ht : On X ((n : ℤ) - 1) t := by
              convert cell_on X k m b using 1; omega
            have htlow (a j : ℕ) (hj : j < m) : t a j = 0 :=
              cell_of_col_ne X b (by omega)
            have hdlt := totalD_below X h v htlow
            have hdeq : totalD X h v t (k + 1) m = z (k + 1) m := by
              change h k m (t k m) + vertical X v t (k + 1) m = _
              have hvzero : vertical X v t (k + 1) m = 0 := by
                cases m with
                | zero => rfl
                | succ m => simp [vertical, htlow _ _ (Nat.lt_succ_self _)]
              rw [hvzero, add_zero]
              simpa only [t, cell_at] using hb
            refine ⟨y + t, hy.add X ht, fun a j hj => by
              simp [hyc a j hj, htlow a j (by omega)], fun a j hj => ?_⟩
            have he : (x - totalD X h v (y + t)) a j = (z - totalD X h v t) a j := by
              dsimp only [z]
              rw [map_add, sub_add_eq_sub_sub]
            rw [he]
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · change z a j - totalD X h v t a j = 0
              have hz0 : z a j = 0 := hlow a j hj
              rw [hz0, hdlt a j hj, sub_zero]
            · by_cases ha : a = k + 1
              · subst a
                change z (k + 1) j - totalD X h v t (k + 1) j = 0
                rw [hdeq, sub_self]
              · apply On.sub X hz (by
                  have hd := On.totalD X h v ht
                  simpa only [show (n : ℤ) - 1 + 1 = n by omega] using hd) a j (by omega)
        · refine ⟨y, hy, hyc, fun a j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hlow a j hj
          · exact hz _ _ (by omega)
      · refine ⟨y, hy, hyc, fun a j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hlow a j hj
        · have hd0 : totalD X h v y a j = 0 := totalD_below X h v hyc a j (by omega)
          change x a j - totalD X h v y a j = 0
          rw [hbelow _ _ (by omega), hd0, sub_zero]
  obtain ⟨y, hy, hyc, he⟩ := step (n + 1)
  refine ⟨y, hy, hyc, ?_⟩
  symm
  apply sub_eq_zero.mp
  funext i j
  by_cases hj : j < n + 1
  · exact he i j hj
  · apply On.sub X hx (by
      have hd := On.totalD X h v hy
      simpa only [show (n : ℤ) - 1 + 1 = n by omega] using hd) i j (by omega)

private theorem totalExact_iff_row
    (hh : ∀ i j x, h (i + 1) j (h i j x) = 0)
    (vv : ∀ i j x, v i (j + 1) (v i j x) = 0)
    (hv : ∀ i j x, h i (j + 1) (v i j x) + v (i + 1) j (h i j x) = 0)
    (hex : ∀ j, 0 < j → RowExact X h j) :
    TotalExact X h v ↔ RowExact X h 0 := by
  constructor
  · intro ht
    have boundary (n : ℕ) (a : X n 0) (ha : h n 0 a = 0) :
        ∃ z, totalD X h v z n 0 = a := by
      let x := cell X n 0 a
      have hx : On X n x := by simpa using cell_on X n 0 a
      have hx0 (i : ℕ) : totalD X h v x i 0 = 0 := by
        cases i with
        | zero => simp [totalD, horizontal, vertical]
        | succ i =>
          change h i 0 (x i 0) + 0 = 0
          by_cases hi : i = n
          · subst i
            simpa [x] using ha
          · have hxi : x i 0 = 0 := hx i 0 (by omega)
            simp [hxi]
      obtain ⟨y, hy, hy0, hdy⟩ := clearColumns X h v hh vv hv 1 (n + 1)
        (fun j hj => hex j (by omega)) _ (by simpa using On.totalD X h v hx)
        (totalD_sq X h v hh vv hv x)
        (fun i j hj => by
          have he : j = 0 := by omega
          subst j
          exact hx0 i)
      have hy' : On X n y := by simpa using hy
      obtain ⟨z, _, hz⟩ := ht n (x - y) (hx.sub X hy') (by rw [map_sub, hdy, sub_self])
      refine ⟨z, ?_⟩
      rw [show totalD X h v z n 0 = (x - y) n 0 from congrFun (congrFun hz n) 0]
      simp [x, hy0 n 0 (by decide)]
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain ⟨z, hz⟩ := boundary 0 a ha
      simpa [totalD, horizontal, vertical] using hz.symm
    · intro n a ha
      obtain ⟨z, hz⟩ := boundary (n + 1) a ha
      exact ⟨z n 0, by simpa [totalD, horizontal, vertical] using hz⟩
  · intro h0 n x hx hd
    obtain ⟨y, hy, _, hdy⟩ := clearColumns X h v hh vv hv 0 n (fun j _ => by
      cases j with
      | zero => exact h0
      | succ j => exact hex _ (Nat.zero_lt_succ j)) x hx hd (by omega)
    exact ⟨y, hy, hdy⟩

private theorem totalD_swap (x : Grid X) (i j : ℕ) :
    totalD (fun j i => X i j) (fun j i => v i j) (fun j i => h i j)
      (fun j i => x i j) j i = totalD X h v x i j := by
  cases i <;> cases j <;> simp [totalD, horizontal, vertical, add_comm]

private theorem totalExact_swap (ht : TotalExact X h v) :
    TotalExact (fun j i => X i j) (fun j i => v i j) (fun j i => h i j) := by
  intro n x hx hd
  obtain ⟨y, hy, hdy⟩ := ht n (fun i j => x j i)
    (fun i j hij => hx j i (by omega)) (by
      funext i j
      rw [← totalD_swap]
      exact congrFun (congrFun hd j) i)
  refine ⟨fun j i => y i j, fun j i hji => hy i j (by omega), ?_⟩
  funext j i
  rw [totalD_swap]
  exact congrFun (congrFun hdy i) j

/-- 第一象限の増大二重複体で、零番以外の行と列が完全なら、零番の行と列の
完全性は同値である（BM18 Lemma 3.4 の二重複体による比較）。 -/
theorem exact_zero_row_iff_zero_col
    (hh : ∀ i j x, h (i + 1) j (h i j x) = 0)
    (vv : ∀ i j x, v i (j + 1) (v i j x) = 0)
    (hv : ∀ i j x, h i (j + 1) (v i j x) + v (i + 1) j (h i j x) = 0)
    (hr : ∀ j, 0 < j → RowExact X h j)
    (hc : ∀ i, 0 < i → ColExact X v i) :
    RowExact X h 0 ↔ ColExact X v 0 := by
  have hrow := totalExact_iff_row X h v hh vv hv hr
  have hcol := totalExact_iff_row (fun j i => X i j) (fun j i => v i j) (fun j i => h i j)
    (fun j i => vv i j) (fun j i => hh i j)
    (fun j i a => by exact (add_comm _ _).trans (hv i j a)) hc
  exact ⟨fun h0 => hcol.mp (totalExact_swap X h v (hrow.mpr h0)),
    fun h0 => hrow.mp (totalExact_swap _ _ _ (hcol.mpr h0))⟩

/-- 二重複体の二方向の微分が可換な規約での比較。列の微分に行次数の符号を入れる。 -/
theorem exact_zero_row_iff_zero_col_of_commute
    (hh : ∀ i j x, h (i + 1) j (h i j x) = 0)
    (vv : ∀ i j x, v i (j + 1) (v i j x) = 0)
    (hv : ∀ i j x, h i (j + 1) (v i j x) = v (i + 1) j (h i j x))
    (hr : ∀ j, 0 < j → RowExact X h j)
    (hc : ∀ i, 0 < i → ColExact X v i) :
    RowExact X h 0 ↔ ColExact X v 0 := by
  classical
  let w (i j : ℕ) := if Even i then v i j else -v i j
  have hcol (i : ℕ) : ColExact X w i ↔ ColExact X v i := by
    by_cases hi : Even i
    · simp [ColExact, w, hi]
    · simp only [ColExact, w, hi, ite_false, AddMonoidHom.neg_apply, neg_eq_zero]
      apply and_congr_right
      intro _
      refine forall_congr' (fun j => forall_congr' (fun x => imp_congr_right (fun _ => ?_)))
      constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨-y, by simpa using hy⟩
  rw [← hcol 0]
  refine exact_zero_row_iff_zero_col X h w hh ?_ ?_ hr (fun i hi => (hcol i).mpr (hc i hi))
  · intro i j x
    by_cases hi : Even i <;> simp [w, hi, vv]
  · intro i j x
    by_cases hi : Even i <;> simp [w, hi, Nat.even_add_one, hv]


end

end SerrePositivity.Cech
