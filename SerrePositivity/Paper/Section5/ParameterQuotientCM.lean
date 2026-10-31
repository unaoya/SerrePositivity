module

public import SerrePositivity.Paper.Section5.ParameterQuotient
public import SerrePositivity.LengthAlgebra.Flat

/-!
# λ-CM 代数に対するパラメータ商の Tor の公式（Lemma 5.3 の λ-CM 版）

## 概要

`lemma_5_3` は、Koszul ホモロジーの消滅 `λ(H_q(x^v; C)) = 0`（`q, v > 0`）と `λ(U) < ∞` を
明示的な入力として受け取る。論文の状況では、これらは `C` が局所環 `D` 上で λ-CM であること
（任意のパラメータ系についての Koszul 消滅と商の有限性、`LengthAlgebra/CohenMacaulay.lean`）と、
`x` の像が `D` のパラメータ系であることから従う。`lemma_5_3_of_cm` はその接続で、解説の命題
「パラメータ商」（Lemma 5.3）の証明に対応する：λ-CM 性から `koszulAcyclic_of_cm` で全ての冪での
消滅を、`hcmfin` から商の有限性を得て、`lemma_5_3` を適用する。

## 規約

係数環の射は `φ = ρ ∘ ι`（`ι : R → D`、`ρ : D → C`）の形で、等式 `hφ` により受け取る。
λ-CM 性は `ρ` についての条件で、`D` のパラメータ系 `y` ごとに `λ(H_i(ρ y; C)) = 0`（`i > 0`）と
`λ(C/(ρ y)) < ∞` を要求する（`CohenMacaulay.lean` の `hzero`、`hfinite` と同じ形）。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity.Section5

open ParamQuot

variable {R D C : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing D] [IsLocalRing D]
  [CommRing C] (ι : R →+* D) (ρ : D →+* C) (φ : R →+* C) (hφ : φ = ρ.comp ι)
  {h : ℕ} (x : Fin h → R) {J : Ideal C} (lam : NormalizedLength C J)
  (hcm : ∀ {n : ℕ} (y : Fin n → D), IsSystemOfParameters D y →
    ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (ρ ∘ y) i) = 0)
  (hcmfin : ∀ {n : ℕ} (y : Fin n → D), IsSystemOfParameters D y →
    lam.len (C ⧸ Ideal.span (Set.range (ρ ∘ y))) ≠ ⊤)
  (hx : IsSystemOfParameters D (ι ∘ x))

include hφ hcm hx in
omit [IsRegularLocalRing R] in
/-- λ-CM 性から、`lemma_5_3` の Koszul 消滅の入力（全ての冪 `x^v` での消滅）を得る。 -/
lemma koszul_zero_of_cm_parameters :
    ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0 := by
  subst hφ
  intro v hv q hq
  have hfun : (fun j ↦ (ρ.comp ι) (x j ^ v)) = (fun j ↦ (ρ ∘ ι ∘ x) j ^ v) :=
    funext fun j ↦ by rw [map_pow]; rfl
  rw [hfun]
  exact LengthAlgebra.koszulAcyclic_of_cm ρ lam hcm (ι ∘ x) hx v hv q hq

include hφ hcmfin hx in
omit [IsRegularLocalRing R] in
/-- λ-CM 性から、`lemma_5_3` のパラメータ商の有限性の入力を得る。 -/
lemma parameterQuotient_len_ne_top_of_cm : lam.len (U φ x) ≠ ⊤ := by
  subst hφ
  rw [lam.len_congr _ _ (Submodule.quotEquivOfEq _ _ (IC_eq (ρ.comp ι) x))]
  exact hcmfin (ι ∘ x) hx

include hφ hcm hcmfin hx in
/-- **Lemma 5.3 の λ-CM 版**：`d = dim R`、`x` は `R` 正則列でその像は `D` のパラメータ系、`C` は
`D` 上 λ-CM、`J` は有限生成で `J^a ⊆ (x)C`、`J ⊆ √((x)C)` なら、有限生成 `B` 加群 `L` について
`λ(Tor_i^B(U, L)) = λ(Tor_i^R(C, L))`、有限、`i + h > d` で `0`。
`lemma_5_3` の Koszul 入力を λ-CM 性から供給したもの。 -/
theorem lemma_5_3_of_cm {d : ℕ} (hd : ringKrullDim R = d)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hfg : J.FG) {a : ℕ} (hJ : J ^ a ≤ IC φ x)
    (hJrad : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (L : Type u) [AddCommGroup L] [Module R L] [Module (B x) L] [IsScalarTower R (B x) L]
    [Module.Finite (B x) L] (i : ℕ) :
    (lamU φ x lam).len (TorAlg (ParamQuot.ψ φ x) i L) = lam.len (TorAlg φ i L) ∧
      lam.len (TorAlg φ i L) ≠ ⊤ ∧ (d < i + h → lam.len (TorAlg φ i L) = 0) :=
  lemma_5_3 φ x lam hd hreg hfg hJ hJrad (koszul_zero_of_cm_parameters ι ρ φ hφ x lam hcm hx)
    (parameterQuotient_len_ne_top_of_cm ι ρ φ hφ x lam hcmfin hx) L i

end SerrePositivity.Section5
