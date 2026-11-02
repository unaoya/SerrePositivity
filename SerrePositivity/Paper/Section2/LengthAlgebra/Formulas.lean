module

public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Formula
public import SerrePositivity.LengthAlgebra.Core

/-! # 長さ代数の値の公式（論文 Theorem 2.5 の (2.5)・(2.6)）

## 概要

正規化長さ `λ` が `D` の全てのパラメータ系 `z` で一乗の商の値 `λ(C/(z)C) = e((z), D)` を持てば、任意の `v ≥ 1` で (2.5) `λ(C/(z^v)C) = v^h e((z), D)` が成り立つ（`parameter_quotient_values_pow`）。さらに正則基底 `A ⊆ D` の重複度の階数公式から (2.6) `λ(C/(t^v)C) = v^h rank_A D` を得る（`base_parameter_values_of_multiplicity`）。

## 方針

成分ごとの冪の重複度公式 `KoszulMultiplicity.multiplicity_parameter_pow` と `HilbertSamuel.multiplicity_eq_rank_of_regular_base` を当てる。

## 規約

代数の構成や標数は仮定しない。Theorem 2.5 の構成（BS・CLMST に届く）を import しないよう、`Paper/Section2/LengthAlgebra` から分けた。

## 使われ方

`Paper/Section2/LengthAlgebra`、`Paper/Section5/Positivity`（LA へ下ろす候補、refactor-plan §10.6）。
-/

public section

universe u

open IsLocalRing
open scoped ENNReal
namespace SerrePositivity.Section2

/-- パラメータ商の一乗での値から、任意の正の冪での (2.5) を導く。 -/
theorem parameter_quotient_values_pow (D C : Type u) [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))) {h : ℕ}
    (hquot : ∀ (z : Fin h → D), IsSystemOfParameters D z →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j))) =
        ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) :
    ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
        ENNReal.ofReal ((v : ℝ) ^ h *
          (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  intro z hz v hv
  rw [hquot _ (hz.pow D v hv), KoszulMultiplicity.multiplicity_parameter_pow D z hz v hv]
  norm_cast

/-- (2.5) と正則基底の重複度の階数公式から (2.6) を得る。 -/
theorem base_parameter_values_of_multiplicity
    (A D C : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    [CommRing C] [Algebra D C]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = h) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hquot : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
        ENNReal.ofReal ((v : ℝ) ^ h *
          (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ))) :
    ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞) := by
  intro v hv
  have hvq := hquot (algebraMap A D ∘ t) hsop v hv
  rw [HilbertSamuel.multiplicity_eq_rank_of_regular_base A D hinj hres t ht hdim hsop] at hvq
  have hc : (v : ℝ) ^ h * (Module.finrank A D : ℝ) =
      ((v ^ h * Module.finrank A D : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [hc, ENNReal.ofReal_natCast] at hvq
  simpa only [Function.comp_apply] using hvq

end SerrePositivity.Section2
