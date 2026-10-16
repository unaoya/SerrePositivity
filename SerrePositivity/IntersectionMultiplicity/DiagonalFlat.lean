module

public import SerrePositivity.IntersectionMultiplicity.DiagonalRing
public import SerrePositivity.HomologicalAlgebra.LocalFlatnessCriterion

/-! # 対角線の環での係数の商の平坦性

## 概要

`R = k[[X]]`、`S = R[[Y]]`（`DiagonalRing`）、素イデアル `P ⊆ R` について、
`D' = S / P S`（`P` は定数として入る）は、変数の取り替え `i₂ : R → S` を通して `R` 上平坦である。

## 方針

`D' ≅ (R/P)[[Y]]` の上で変数 `Y` は弱正則列（`isWeaklyRegular_quotient_map_C_ofFn_X`）。
`i₂(X_i) = Y_i` なので `R` の極大イデアルを生成する `X` は `D'` 上の弱正則列で、
局所平坦性判定法（`flat_of_isWeaklyRegular`）から平坦。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（$R[[Y]]/P$ の平坦性）。
`D' ⊗_{R, i₂} −` が完全関手であることを、`E = R/Q` の自由分解の移送に使う。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing MvPowerSeries

namespace SerrePositivity.DiagonalRing

variable (k : Type u) [Field k] (d : ℕ)

local notation "𝓡" => MvPowerSeries (Fin d) k

/-- 係数の商 `D' = S / P S`（`P` は定数として入る）。 -/
abbrev coeffQuot (P : Ideal 𝓡) : Type u := DiagonalRing k d ⧸ P.map (const k d)

theorem ofList_ofFn_X : Ideal.ofList (List.ofFn (X : Fin d → 𝓡)) = maximalIdeal 𝓡 := by
  rw [← mvPowerSeries_span_X_eq_maximalIdeal]
  unfold Ideal.ofList
  congr 1
  ext r
  simp [List.mem_ofFn]

/-- **係数の商の平坦性**：`D' = S / P S` は `i₂` を通して `R` 上平坦。 -/
theorem flat_coeffQuot (P : Ideal 𝓡) : Module.Flat 𝓡 (coeffQuot k d P) := by
  have hA := isWeaklyRegular_of_span_eq_maximalIdeal 𝓡 (X : Fin d → 𝓡)
    (mvPowerSeries_span_X_eq_maximalIdeal k d) (ringKrullDim_mvPowerSeries_field k d)
  apply flat_of_isWeaklyRegular (B := DiagonalRing k d) (coeffQuot k d P) (List.ofFn X)
    (ofList_ofFn_X k d) hA
  rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (DiagonalRing k d)]
  have hmap : (List.ofFn (X : Fin d → 𝓡)).map (algebraMap 𝓡 (DiagonalRing k d)) =
      List.ofFn (var k d) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact algebraMap_X k d i
  rw [hmap]
  exact isWeaklyRegular_quotient_map_C_ofFn_X P (IsNoetherian.noetherian P) d

end SerrePositivity.DiagonalRing
