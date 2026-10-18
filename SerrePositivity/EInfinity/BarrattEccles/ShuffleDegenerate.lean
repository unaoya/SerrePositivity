module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleComponent
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEdges

/-!
# shuffle 合成と退化単体

概要：Berger–Fresse §1.1.3 の shuffle 合成が退化単体を零とする関係と両立することを示す。
方針：重複した隣接頂点を結ぶ座標辺を経路へ持ち上げ、合成単体の重複頂点を得る。
規約：各経路の項が個別に退化するため、この部分には符号の相殺を使わない。
使われ方：shuffle の双線形写像の公式を任意の単体生成元について成立させる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：第一の入力が退化すると各 shuffle 単体も退化する（Berger–Fresse §1.1.3）。
方針：入力の重複頂点を結ぶ水平辺を持ち上げ、その辺の合成頂点の一致を示す。
規約：arity や単体次数が零の場合も含む。
使われ方：第一の入力に関する正規化の関係を保証する。 -/
lemma shuffleSimplex_degenerate_left (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (hx : x ∈ (simplicial (m + 1)).degenerate p) :
    shuffleSimplex m n i s x y ∈ (simplicial (m + n)).degenerate (p + q) := by
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate, mem_nonDegenerate_iff] at hx ⊢
  push Not at hx
  obtain ⟨j, hj⟩ := hx
  obtain ⟨k, h₀, h₁, hv⟩ := s.horizontal_edge j
  intro h
  apply h k
  simp only [simplexEquiv_shuffleSimplex]
  rw [h₀, h₁, hv, hj]

/-- 概要：第二の入力が退化すると各 shuffle 単体も退化する（Berger–Fresse §1.1.3）。
方針：入力の重複頂点を結ぶ垂直辺を持ち上げ、その辺の合成頂点の一致を示す。
規約：どの shuffle 経路の項も個別に退化する。
使われ方：第二の入力に関する正規化の関係を保証する。 -/
lemma shuffleSimplex_degenerate_right (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (hy : y ∈ (simplicial n).degenerate q) :
    shuffleSimplex m n i s x y ∈ (simplicial (m + n)).degenerate (p + q) := by
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate, mem_nonDegenerate_iff] at hy ⊢
  push Not at hy
  obtain ⟨j, hj⟩ := hy
  obtain ⟨k, h₀, h₁, hh⟩ := s.vertical_edge j
  intro h
  apply h k
  simp only [simplexEquiv_shuffleSimplex]
  rw [h₀, h₁, hh, hj]

variable (A : Type u) [CommRing A]

/-- 概要：第一の入力が退化すると shuffle 和は零である（Berger–Fresse §1.1.3）。
方針：各項の合成単体が退化するため、正規化生成元の消滅を使う。
規約：符号の値に依存しない消滅である。
使われ方：双線形合成の生成元の公式を退化入力へ拡張する。 -/
lemma shuffleValue_degenerate_left (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (hx : x ∈ (simplicial (m + 1)).degenerate p) : shuffleValue A m n i p q x y = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [normalizedGenerator_degenerate A (m + n) (p + q) _
    (shuffleSimplex_degenerate_left m n i s x y hx), smul_zero]

/-- 概要：第二の入力が退化すると shuffle 和は零である（Berger–Fresse §1.1.3）。
方針：各項の合成単体が退化するため、正規化生成元の消滅を使う。
規約：shuffle 和の値は任意の可換基礎環で零となる。
使われ方：双線形合成の生成元の公式を退化入力へ拡張する。 -/
lemma shuffleValue_degenerate_right (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (hy : y ∈ (simplicial n).degenerate q) : shuffleValue A m n i p q x y = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [normalizedGenerator_degenerate A (m + n) (p + q) _
    (shuffleSimplex_degenerate_right m n i s x y hy), smul_zero]

/-- 概要：双線形合成は任意の単体生成元で shuffle 和の公式を満たす（Berger–Fresse §1.1.3）。
方針：非退化入力では基底上の定義を使い、退化入力では両辺の消滅を使う。
規約：入力単体の非退化性を仮定しない。
使われ方：微分が生む退化した面を含めて、shuffle の鎖写像の条件を計算する。 -/
lemma shuffleBilinear_generators (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    shuffleBilinear A m n i p q (normalizedGenerator A (m + 1) p x)
      (normalizedGenerator A n q y) = shuffleValue A m n i p q x y := by
  classical
  by_cases hx : x ∈ (simplicial (m + 1)).nonDegenerate p
  · by_cases hy : y ∈ (simplicial n).nonDegenerate q
    · exact shuffleBilinear_nondegenerate A m n i p q ⟨x, hx⟩ ⟨y, hy⟩
    · have hy' := (SSet.mem_degenerate_iff_notMem_nonDegenerate _ _).2 hy
      rw [normalizedGenerator_degenerate A n q y hy', map_zero,
        shuffleValue_degenerate_right A m n i p q x y hy']
  · have hx' := (SSet.mem_degenerate_iff_notMem_nonDegenerate _ _).2 hx
    rw [normalizedGenerator_degenerate A (m + 1) p x hx', map_zero,
      LinearMap.zero_apply, shuffleValue_degenerate_left A m n i p q x y hx']

end SerrePositivity.EInfinity.BarrattEccles
