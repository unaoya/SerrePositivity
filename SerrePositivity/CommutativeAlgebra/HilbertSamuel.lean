module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import SerrePositivity.CommutativeAlgebra.HilbertSeries
public import SerrePositivity.CommutativeAlgebra.ReesPresentation

/-!
# Hilbert–Samuel 多項式と重複度

定義と基本性質は `HilbertSamuelBasic.lean`、随伴次数加群と Rees 加群の
構成は `AssociatedGraded.lean`・`ReesModule.lean`・`ReesPresentation.lean` に置く。

`HilbertSeries.lean` は Hilbert 級数の有理型表示から Samuel 多項式を構成する。
一般の多項式性に残る未証明箇所は、その有理型表示を有限生成性から得る
Hilbert–Serre の部分である。次元定理も未証明として残る。

重複度のイデアル冪の公式は多項式性と定義から、正値性は多項式性と次元定理から証明する。
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity

namespace HilbertSamuel

variable (D : Type u) [CommRing D]

section statements

variable [IsNoetherianRing D] [IsLocalRing D]

/-- **Hilbert–Samuel の定理**：`I = (x₁, …, x_s)` が `m_D` 準素で `M` が有限生成なら、Samuel 関数は
十分大きい `n` で次数 `≤ s` の多項式の値に等しい。`gr_I(M)` が `(D/I)[X₁, …, X_s]` 上有限生成な
次数つき加群であることと、Hilbert の定理（Poincaré 級数が `p(X)/(1−X)^s`）による
（Atiyah–Macdonald Prop. 11.4、Thm 11.1）。 -/
theorem exists_isSamuelPoly (I : Ideal D) (hI : I.radical = maximalIdeal D)
    {s : ℕ} (x : Fin s → D) (hx : I = Ideal.span (Set.range x))
    (M : Type u) [AddCommGroup M] [Module D M] [Module.Finite D M] :
    ∃ P : ℚ[X], IsSamuelPoly D I M P ∧ P.natDegree ≤ s := by
  sorry

/-- イデアル自体の冪について `e(I^v, M) = v^(dim M) e(I, M)`。
多項式性と定義から従い、次元定理は不要。
パラメータの成分ごとの冪の公式とは区別する。 -/
theorem multiplicity_pow
    (M : Type u) [AddCommGroup M] [Module D M] [Module.Finite D M]
    (I : Ideal D) (hI : I.radical = maximalIdeal D) (v : ℕ) (hv : 0 < v) :
    multiplicity D (I ^ v) M =
      (v : ℚ) ^ dimToNat (Module.supportDim D M) * multiplicity D I M := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨P, hP, _⟩ := exists_isSamuelPoly D I hI x hx.symm M
  have hpoly := isSamuelPoly_poly D ⟨P, hP⟩
  have heq := poly_eq D (IsSamuelPoly.pow D M hpoly v hv)
  dsimp only [multiplicity]
  rw [heq, comp_C_mul_X_coeff]
  ring

/-- **次元定理**：`I` が `m_D` 準素なら `D` 自身の Samuel 多項式の次数は `dim D`
（Atiyah–Macdonald Thm 11.14、`d(D) = dim D` の部分）。 -/
theorem natDegree_poly_eq_dim (I : Ideal D) (hI : I.radical = maximalIdeal D) :
    (poly D I D).natDegree = dimToNat (ringKrullDim D) := by
  sorry

/-- **正値性**：`I` が `m_D` 準素なら `0 < e(I, D)`。Samuel 多項式の次数が `dim D` で、
十分大きな正の整数で正値をとる多項式の最高次係数は正だから。 -/
theorem multiplicity_pos (I : Ideal D) (hI : I.radical = maximalIdeal D) :
    0 < multiplicity D I D := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨P, hP, _⟩ := exists_isSamuelPoly D I hI x hx.symm D
  have hp := isSamuelPoly_poly D ⟨P, hP⟩
  dsimp only [multiplicity]
  rw [Module.supportDim_self_eq_ringKrullDim, ← natDegree_poly_eq_dim D I hI,
    coeff_natDegree]
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (IsSamuelPoly.leadingCoeff_pos D hI hp)

/-- パラメータ系 `z` について `0 < e((z), D)`（`multiplicity_pos` の特別な場合）。 -/
theorem multiplicity_pos_of_isSystemOfParameters {h : ℕ} (z : Fin h → D)
    (hz : IsSystemOfParameters D z) :
    0 < multiplicity D (Ideal.span (Set.range z)) D :=
  multiplicity_pos D _ hz.2

end statements

end HilbertSamuel

end SerrePositivity
