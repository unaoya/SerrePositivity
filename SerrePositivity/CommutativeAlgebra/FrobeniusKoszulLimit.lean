module

public import SerrePositivity.CommutativeAlgebra.KoszulFiniteLength
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Frobenius ホモロジーの消滅定理の Koszul 複体への適用

Roberts の定理を使う際の有限自由性・振幅・ホモロジーの有限長性を、
パラメータ系から確認する。Frobenius 基底変更をパラメータの冪と同定し、
実数値の消滅極限を正規化長さで使う `ℝ≥0∞` 値の極限へ移す。
一般の消滅定理そのものは明示した仮定であり、ここでは引用や新しい `sorry` を置かない。
完備局所環についての文献の主張との対応は `notes/section-2.md` に記録している。
-/

public section

universe u

namespace SerrePositivity

open CategoryTheory Limits Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Frobenius 基底変更した Koszul 複体のホモロジーの長さは、パラメータの冪のものに等しい。
基底変更と Koszul 複体の同型を使い、Frobenius の平坦性は要求しない。 -/
theorem length_frobenius_koszulHomology
    (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    {h : ℕ} (z : Fin h → D) (n : ℕ) (i : ℤ) :
    Module.length D ((baseChange (iterateFrobenius D p n) (koszulComplex z)).homology i) =
      Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) := by
  exact ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (baseChangeKoszulIso (iterateFrobenius D p n) z)).toLinearEquiv.length_eq

/-- 長さが環の次元に等しい有限自由複体に対する Roberts 型の消滅から、
パラメータ系の正規化 Frobenius Koszul ホモロジーの消滅を導く。
一般定理の実数値の結論を仮定として明示し、適用条件と値域の変換を証明する。 -/
theorem normalized_frobenius_koszul_tendsto_of_homology_vanishing
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (hRoberts : ∀ d : ℕ, ringKrullDim D = d →
      ∀ K : CochainComplex (ModuleCat.{u} D) ℤ,
        (∀ j, Module.Free D (K.X j) ∧ Module.Finite D (K.X j)) →
        (∀ j, j < -(d : ℤ) ∨ 0 < j → IsZero (K.X j)) →
        (∀ j, IsFiniteLength D (K.homology j)) →
        ∀ i : ℕ, 0 < i → Tendsto (fun n : ℕ ↦
          ((Module.length D
            ((baseChange (iterateFrobenius D p n) K).homology (-(i : ℤ)))).toNat : ℝ) /
              (p : ℝ) ^ (n * d)) atTop (nhds 0))
    {h : ℕ} (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (i : ℕ) (hi : 0 < i) :
    Tendsto (fun n : ℕ ↦
      (Module.length D (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) : ℝ≥0∞) /
        (p : ℝ≥0∞) ^ (n * h)) atTop (nhds 0) := by
  have hreal := hRoberts h hz.1 (koszulComplex z)
    (koszulComplex_free_finite_X z)
    (fun j hj ↦ hj.elim (koszulComplex_isZero_X_of_lt z j)
      (koszulComplex_isZero_X_of_pos z j))
    (isFiniteLength_koszulHomology_of_isSystemOfParameters D z hz) i hi
  simp only [length_frobenius_koszulHomology] at hreal
  have hfinite n : Module.length D
      (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_koszulHomology_of_isSystemOfParameters D _
        (hz.pow D _ (pow_pos (Fact.out : p.Prime).pos n)) (-(i : ℤ)))
  apply (ENNReal.tendsto_toReal_iff (fun n ↦ ENNReal.div_ne_top
    (ENat.toENNReal_ne_top.mpr (hfinite n))
    (pow_ne_zero (n * h) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)))
    ENNReal.zero_ne_top).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    toReal_toENNReal, ENNReal.toReal_zero] using hreal

end SerrePositivity
