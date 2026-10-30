module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Basic
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Polynomial
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Dimension

/-!
# Hilbert–Samuel 多項式と重複度

定義と基本性質は `HilbertSamuelBasic.lean`、随伴次数加群と Rees 加群の
構成は `AssociatedGraded.lean`・`ReesModule.lean`・`ReesPresentation.lean` に置く。

`HilbertSerre.lean` の数値版を実際の随伴次数加群へ適用し、
`HilbertSamuelPolynomial.lean` で有理型の Hilbert 級数を得る。
`HilbertSeries.lean` の多項式の構成へ接続して、一般の多項式性を証明する。
`HilbertSamuelDimension.lean` で、パラメータ系による上界と、Artin–Rees・
素イデアルの鎖による下界から次数と Krull 次元の一致を証明する。

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
