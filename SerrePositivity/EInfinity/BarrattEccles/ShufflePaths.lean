module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max

/-!
# shuffle の格子経路

概要：Berger–Fresse §1.1.3 の合成公式を添字づける (p,q) 格子経路を構成する。
方針：p+q 本の辺のうち水平辺の位置を選び、各頂点までの水平辺と垂直辺を数える。
規約：頂点は 0 から p+q、辺は 0 から p+q−1 で添字づける。
使われ方：shuffle の二つの退化写像と、その符号を定める入力となる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：(p,q) 格子経路の水平辺の位置（Berger–Fresse §1.1.3）。
方針：p+q 個の辺から p 個の水平辺を選ぶ。
規約：選ばれなかった辺は垂直辺である。
使われ方：shuffle の有限和の添字集合となる。 -/
abbrev ShufflePath (p q : ℕ) := {s : Finset (Fin (p + q)) // s.card = p}

/-- 概要：指定頂点より前にある辺の集合（Berger–Fresse §1.1.3）。
方針：辺の番号が頂点番号より小さいという条件で取る。
規約：最後の頂点では全ての辺を含む。
使われ方：格子経路の座標の和を計算する。 -/
def prefixPositions {N : ℕ} (k : Fin (N + 1)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val < k.val)

/-- 概要：頂点 k までの辺の個数は k である（Berger–Fresse §1.1.3）。
方針：最後の頂点とそれ以外に分け、有限順序の初期区間を数える。
規約：N=0 の経路も含む。
使われ方：水平・垂直座標の和を与える。 -/
lemma prefixPositions_card {N : ℕ} (k : Fin (N + 1)) : (prefixPositions k).card = k.val := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [prefixPositions]
  · have h : prefixPositions j.castSucc = Finset.Iio j := by
      ext i
      simp [prefixPositions]
    rw [h, Fin.card_Iio]
    rfl

/-- 概要：経路の垂直辺の個数は q である（Berger–Fresse §1.1.3）。
方針：全辺数から水平辺数を引く。
規約：補集合は Fin(p+q) の中で取る。
使われ方：垂直座標の上界を保証する。 -/
lemma ShufflePath.compl_card {p q : ℕ} (s : ShufflePath p q) : s.valᶜ.card = q := by
  simp [Finset.card_compl, s.property]

/-- 概要：格子経路の水平座標の単調写像（Berger–Fresse §1.1.3）。
方針：指定頂点より前にある水平辺を数える。
規約：値は 0 から p の有限順序に属する。
使われ方：shuffle に現れる最初の単体の引き戻しを定める。 -/
def ShufflePath.horizontal {p q : ℕ} (s : ShufflePath p q) :
    Fin (p + q + 1) →o Fin (p + 1) where
  toFun k := ⟨(s.val.filter (fun i => i.val < k.val)).card,
    Nat.lt_succ_of_le (by
      simpa only [s.property] using s.val.card_filter_le (fun i => i.val < k.val))⟩
  monotone' i j hij := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

/-- 概要：格子経路の垂直座標の単調写像（Berger–Fresse §1.1.3）。
方針：指定頂点より前にある垂直辺を数える。
規約：値は 0 から q の有限順序に属する。
使われ方：shuffle に現れる第二の単体の引き戻しを定める。 -/
def ShufflePath.vertical {p q : ℕ} (s : ShufflePath p q) :
    Fin (p + q + 1) →o Fin (q + 1) where
  toFun k := ⟨(s.valᶜ.filter (fun i => i.val < k.val)).card,
    Nat.lt_succ_of_le (by simpa only [s.compl_card] using
      s.valᶜ.card_filter_le (fun i => i.val < k.val))⟩
  monotone' i j hij := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

/-- 概要：格子経路の二座標の和は頂点番号である（Berger–Fresse §1.1.3）。
方針：前にある辺を水平辺とその補集合に分割して数える。
規約：有限順序の値を自然数として足す。
使われ方：隣接頂点のステップと経路の頂点の単射性を導く。 -/
lemma ShufflePath.coordinate_sum {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (s.horizontal k).val + (s.vertical k).val = k.val := by
  change (s.val.filter (fun i => i.val < k.val)).card +
    (s.valᶜ.filter (fun i => i.val < k.val)).card = k.val
  have h₁ : s.val.filter (fun i => i.val < k.val) =
      (prefixPositions k).filter (fun i => i ∈ s.val) := by
    ext i
    simp [prefixPositions, and_comm]
  have h₂ : s.valᶜ.filter (fun i => i.val < k.val) =
      (prefixPositions k).filter (fun i => i ∉ s.val) := by
    ext i
    simp [prefixPositions, and_comm]
  rw [h₁, h₂, Finset.card_filter_add_card_filter_not, prefixPositions_card]

/-- 概要：格子経路は同じ頂点を二度通らない（Berger–Fresse §1.1.3）。
方針：二座標の和が頂点番号であることを使う。
規約：座標対としての単射性を述べる。
使われ方：shuffle 単体の非退化性の検討に用いる。 -/
lemma ShufflePath.vertex_injective {p q : ℕ} (s : ShufflePath p q) :
    Function.Injective (fun k => (s.horizontal k, s.vertical k)) := by
  intro i j h
  have hx := congrArg (fun z => z.1.val + z.2.val) h
  rw [s.coordinate_sum, s.coordinate_sum] at hx
  exact Fin.ext hx

/-- 概要：格子経路の各辺は水平または垂直の単位ステップである（Berger–Fresse §1.1.3）。
方針：単調性と二座標の和の増分が 1 であることを組み合わせる。
規約：castSucc は辺の始点、succ は終点。
使われ方：shuffle の境界項の分類に用いる。 -/
lemma ShufflePath.unit_step {p q : ℕ} (s : ShufflePath p q) (i : Fin (p + q)) :
    ((s.horizontal i.succ).val = (s.horizontal i.castSucc).val + 1 ∧
      s.vertical i.succ = s.vertical i.castSucc) ∨
    (s.horizontal i.succ = s.horizontal i.castSucc ∧
      (s.vertical i.succ).val = (s.vertical i.castSucc).val + 1) := by
  have h₀ := s.coordinate_sum i.castSucc
  have h₁ := s.coordinate_sum i.succ
  have hx := s.horizontal.monotone i.castSucc_le_succ
  have hy := s.vertical.monotone i.castSucc_le_succ
  simp only [Fin.ext_iff]
  change (s.horizontal i.castSucc).val ≤ (s.horizontal i.succ).val at hx
  change (s.vertical i.castSucc).val ≤ (s.vertical i.succ).val at hy
  simp only [Fin.val_castSucc, Fin.val_succ] at h₀ h₁
  omega

/-- 概要：水平座標を単体圏の射にする（Berger–Fresse §1.1.3）。
方針：単調写像から単体圏の射を作る。
規約：向きは [p+q] → [p]。
使われ方：第一の単体を p+q 次元へ退化させる。 -/
def ShufflePath.horizontalMap {p q : ℕ} (s : ShufflePath p q) : ⦋p + q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom s.horizontal

/-- 概要：垂直座標を単体圏の射にする（Berger–Fresse §1.1.3）。
方針：単調写像から単体圏の射を作る。
規約：向きは [p+q] → [q]。
使われ方：第二の単体を p+q 次元へ退化させる。 -/
def ShufflePath.verticalMap {p q : ℕ} (s : ShufflePath p q) : ⦋p + q⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom s.vertical

/-- 概要：水平座標は最初と最後の頂点を保つ（Berger–Fresse §1.1.3）。
方針：空の接頭区間と全辺の接頭区間を数える。
規約：終点の水平座標は p。
使われ方：水平座標写像の全射性を導く。 -/
lemma ShufflePath.horizontal_endpoints {p q : ℕ} (s : ShufflePath p q) :
    s.horizontal 0 = 0 ∧ s.horizontal (Fin.last (p + q)) = Fin.last p := by
  constructor
  · apply Fin.ext
    change (s.val.filter (fun i => i.val < 0)).card = 0
    simp
  · apply Fin.ext
    change (s.val.filter (fun i => i.val < p + q)).card = p
    simpa using s.property

/-- 概要：垂直座標は最初と最後の頂点を保つ（Berger–Fresse §1.1.3）。
方針：空の接頭区間と全垂直辺の個数を数える。
規約：終点の垂直座標は q。
使われ方：垂直座標写像の全射性を導く。 -/
lemma ShufflePath.vertical_endpoints {p q : ℕ} (s : ShufflePath p q) :
    s.vertical 0 = 0 ∧ s.vertical (Fin.last (p + q)) = Fin.last q := by
  constructor
  · apply Fin.ext
    change (s.valᶜ.filter (fun i => i.val < 0)).card = 0
    simp
  · apply Fin.ext
    change (s.valᶜ.filter (fun i => i.val < p + q)).card = q
    simpa using s.compl_card

/-- 概要：端点を保ち一度に高々 1 だけ増える有限順序の写像は全射である（Berger–Fresse §1.1.3）。
方針：指定値以上になる最初の頂点を取り、その直前との増分で一致を示す。
規約：写像の単調性は仮定せず、増分の上界と端点だけを使う。
使われ方：shuffle の座標写像が退化を表す全射であることを証明する。 -/
lemma fin_surjective_of_unit_steps {N P : ℕ} (f : Fin (N + 1) → Fin (P + 1))
    (hzero : f 0 = 0) (hlast : f (Fin.last N) = Fin.last P)
    (hstep : ∀ i : Fin N, (f i.succ).val ≤ (f i.castSucc).val + 1) :
    Function.Surjective f := by
  intro y
  let S := Finset.univ.filter (fun k => y ≤ f k)
  have hS : S.Nonempty := ⟨Fin.last N, by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hlast]
    exact Fin.le_last _⟩
  let k := S.min' hS
  have hk : k ∈ S := S.min'_mem hS
  have hy : y ≤ f k := (Finset.mem_filter.mp hk).2
  by_cases hk₀ : k = 0
  · refine ⟨0, ?_⟩
    rw [hk₀, hzero] at hy
    exact hzero.trans (le_antisymm hy (Fin.zero_le _)).symm
  · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hk₀
    have hj' : ¬ y ≤ f j.castSucc := by
      intro h
      have hm := S.min'_le j.castSucc (by simp [S, h])
      change k ≤ j.castSucc at hm
      rw [hj] at hm
      exact (not_le_of_gt j.castSucc_lt_succ) hm
    refine ⟨j.succ, Fin.ext ?_⟩
    have hs := hstep j
    rw [hj] at hy
    change y.val ≤ (f j.succ).val at hy
    change ¬ y.val ≤ (f j.castSucc).val at hj'
    omega

/-- 概要：shuffle の水平座標写像は全射である（Berger–Fresse §1.1.3）。
方針：端点の保存と単位ステップを用いる。
規約：全射は有限順序の台の関数について述べる。
使われ方：水平写像が単体圏の全射であることを与える。 -/
lemma ShufflePath.horizontal_surjective {p q : ℕ} (s : ShufflePath p q) :
    Function.Surjective s.horizontal := by
  apply fin_surjective_of_unit_steps s.horizontal
    s.horizontal_endpoints.1 s.horizontal_endpoints.2
  intro i
  rcases s.unit_step i with h | h
  · omega
  · have hx := congrArg Fin.val h.1
    omega

/-- 概要：shuffle の垂直座標写像は全射である（Berger–Fresse §1.1.3）。
方針：端点の保存と単位ステップを用いる。
規約：水平座標との入れ替えで符号はまだ導入しない。
使われ方：垂直写像が単体圏の全射であることを与える。 -/
lemma ShufflePath.vertical_surjective {p q : ℕ} (s : ShufflePath p q) :
    Function.Surjective s.vertical := by
  apply fin_surjective_of_unit_steps s.vertical s.vertical_endpoints.1 s.vertical_endpoints.2
  intro i
  rcases s.unit_step i with h | h
  · have hy := congrArg Fin.val h.2
    omega
  · omega

/-- 概要：shuffle の水平写像は単体圏で epi である（Berger–Fresse §1.1.3）。
方針：全射な単調写像による epi の判定を使う。
規約：単体の引き戻しでは退化写像として現れる。
使われ方：正規化鎖の shuffle の退化列を表す。 -/
instance ShufflePath.horizontalMap_epi {p q : ℕ} (s : ShufflePath p q) : Epi s.horizontalMap :=
  SimplexCategory.epi_iff_surjective.mpr s.horizontal_surjective

/-- 概要：shuffle の垂直写像は単体圏で epi である（Berger–Fresse §1.1.3）。
方針：全射な単調写像による epi の判定を使う。
規約：単体の引き戻しでは退化写像として現れる。
使われ方：正規化鎖の shuffle の退化列を表す。 -/
instance ShufflePath.verticalMap_epi {p q : ℕ} (s : ShufflePath p q) : Epi s.verticalMap :=
  SimplexCategory.epi_iff_surjective.mpr s.vertical_surjective

end SerrePositivity.EInfinity.BarrattEccles
