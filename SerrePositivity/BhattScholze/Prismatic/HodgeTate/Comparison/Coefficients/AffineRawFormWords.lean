module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineFormsCoefficientBasis
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
import all SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
import all SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz

/-!
# 元の通常形式の座標外積の表示

## 概要
単項式と外積の基底を、零次形式に座標一次形式を順に掛けたものとして読む。

## 方針
元の外冪の ιMulti の零次・後続次数の式を使う。

## 規約
外積の順序は元の並べた基底の添字と同じに保つ。

## 使われ方
元の標準 HT 写像の自然性を、零次と座標一次から基底全体へ移す。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.DeRham
variable (k T : Type u) [CommRing k] [Fintype T] [DecidableEq T]

/-- 元の多項式係数と座標一次形式の順序付き外積。 -/
def coordinateFormWord (n : ℕ) (v : Fin n → T) (g : Poly k T) : forms k T n :=
  g ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Pi.single (v j) 1)

/-- 長さ零の座標外積は元の零次形式。 -/
theorem coordinateFormWord_zero (v : Fin 0 → T) (g : Poly k T) :
    coordinateFormWord k T 0 v g = formsZeroEquiv k T g := by
  rw [coordinateFormWord, formsZeroEquiv_tmul]
  congr 1
  apply Subtype.ext
  simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
    exteriorPower.zeroEquiv, ExteriorAlgebra.ιMulti_apply]

/-- 座標外積は、先頭の座標一次形式と残りの外積に分かれる。 -/
theorem coordinateFormWord_succ (n : ℕ) (v : Fin (n + 1) → T) (g : Poly k T) :
    coordinateFormWord k T (n + 1) v g =
      cast (congrArg (forms k T) (Nat.add_comm 1 n))
        (wedge k T (dX k T (v 0)) (coordinateFormWord k T n (Matrix.vecTail v) g)) := by
  rw [dX, coordinateFormWord, coordinateFormWord, wedge_tmul', one_mul,
    cast_tmul (Nat.add_comm 1 n)]
  congr 1
  apply Subtype.ext
  rw [cast_exterior_val (Nat.add_comm 1 n)]
  simp [exteriorWedge, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]

variable [LinearOrder T]
/-- 元の単項式・外積基底は、同じ順序付き座標外積である。 -/
theorem polynomialFormsBasis_coordinateFormWord (i : ℕ)
    (v : (T →₀ ℕ) × Set.powersetCard T i) :
    polynomialFormsBasis k T i v =
      coordinateFormWord k T i (Set.powersetCard.ofFinEmbEquiv.symm v.2)
        (MvPolynomial.monomial v.1 1) := by
  rw [polynomialFormsBasis, Module.Basis.tensorProduct_apply', MvPolynomial.coe_basisMonomials]
  unfold coordinateFormWord
  congr 1
  apply Subtype.ext
  simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_family,
    Function.comp_def, Pi.basisFun_apply]

end SerrePositivity.DeRham
