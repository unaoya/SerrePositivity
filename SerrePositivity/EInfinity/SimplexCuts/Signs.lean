module

public import SerrePositivity.EInfinity.SimplexCuts.Outputs
public import SerrePositivity.EInfinity.Surjection.Caesuras

/-!
# 一般の区間切断の BF 符号

Berger–Fresse §2.2.3–6。水平座標の fiber の両端から各区間の長さを読む。
内側区間の追加の一、逆転対の交換符号、右端点の位置符号を保持する。
区間専用の符号や作用は変更しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 一つの切断区間の展開位置。水平座標の全射性により空ではない。 -/
def intervalPositions {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    Finset (Fin (m + q + 1)) := Finset.univ.filter (fun j => s.horizontal j = i)

/-- lo・hi の定義に必要な非空性。既存の水平座標の全射性を評価する。 -/
lemma intervalPositions_nonempty {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    (intervalPositions s i).Nonempty := by
  obtain ⟨j, hj⟩ := s.horizontal_surjective i
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

def lo {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) : ℕ :=
  (s.vertical ((intervalPositions s i).min' (intervalPositions_nonempty s i))).val

def hi {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) : ℕ :=
  (s.vertical ((intervalPositions s i).max' (intervalPositions_nonempty s i))).val

/-- 内側区間では幾何学的長さに一を足す（BF §2.2.3）。 -/
def intervalLength {m q r : ℕ} (s : Cut m q) (u : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) : ℕ := hi s i - lo s i + if Surjection.Caesura u i then 1 else 0

/-- 色の順に区間を並べ替える Koszul 指数（BF §2.2.4）。 -/
def permutationExponent {m q r : ℕ} (s : Cut m q) (u : Fin (m + 1) → Fin r) : ℕ :=
  ∑ i, ∑ j, if i < j ∧ u j < u i then intervalLength s u i * intervalLength s u j else 0

/-- 内側区間の右端点による符号の指数（BF §2.2.4）。 -/
def positionExponent {m q r : ℕ} (s : Cut m q) (u : Fin (m + 1) → Fin r) : ℕ :=
  ∑ i, if Surjection.Caesura u i then hi s i else 0

/-- 全整数係数を持つ一般の切断の符号（BF §2.2.4–6）。 -/
def cutSign {m q r : ℕ} (s : Cut m q) (u : Fin (m + 1) → Fin r) : ℤ :=
  (-1) ^ (permutationExponent s u + positionExponent s u)

end SerrePositivity.EInfinity.SimplexCuts
