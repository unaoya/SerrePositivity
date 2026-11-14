module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamCoefficientProjection
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnBaseChange
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamCoefficientProjection
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDRawFormsBaseChange
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 分冪列の係数変更と完備化単位

## 概要
完備列の実際の半線形な係数変更は、自由模型の係数変更と可換である。

## 方針
純テンソル上で環の完備化単位の自然性と外冪の係数変更を照合する。

## 規約
余単体次数を固定し、標的の係数を制限して余鎖写像として読む。

## 使われ方
BS 著者版 Theorem 6.4 の完備導来底変換を、指定された Witt 比較射と照合する。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (r : ℕ) (n : SimplexCategory)

local notation "res" => ModuleCat.restrictScalars (algebraMap A B)
local notation "R" => Functor.mapHomologicalComplex res (ComplexShape.up ℕ)

/-- 任意の列における完備形式の係数変更。 -/
def pdCompletedColumnCoefficientHom :
    pdDeRhamColumn p A r n ⟶ Functor.obj R (pdDeRhamColumn p B r n) :=
  CochainComplex.ofHom (fun j =>
    ModuleCat.semilinearMapAddEquiv (algebraMap A B) _ _
      (pdFormsCoefficientMap p A B r n j)) (by
      intro j
      change _ ≫ (res).map ((pdDeRhamColumn p B r n).d j (j + 1)) =
        (pdDeRhamColumn p A r n).d j (j + 1) ≫ _
      rw [column_d_eq, column_d_eq]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (pdFormsCoefficientMap_d p A B r n j x).symm)

private theorem coefficient_unit :
    pdColumnCompletionUnit p A r n ≫ pdCompletedColumnCoefficientHom p A B r n =
      pdUncompletedColumnCoefficientHom A B r n ≫
        (R).map (pdColumnCompletionUnit p B r n) := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a w
  change pdFormsCoefficientMap p A B r n j
      (TensorProduct.map (columnUnitCoeff p A r n) LinearMap.id (a ⊗ₜ[A] w)) =
    TensorProduct.map (columnUnitCoeff p B r n) LinearMap.id
      (pdRawFormsCoefficientMap A B r n.len j (a ⊗ₜ[A] w))
  change pdTermCoefficientMap p A B r n.len (columnUnitCoeff p A r n a) ⊗ₜ[B]
      exteriorPowerCoefficients A B (Fin r × Fin (n.len + 1)) j w =
    columnUnitCoeff p B r n (pdRawCoefficients A B r n.len a) ⊗ₜ[B]
      exteriorPowerCoefficients A B (Fin r × Fin (n.len + 1)) j w
  exact congrArg
    (fun z => z ⊗ₜ[B] exteriorPowerCoefficients A B (Fin r × Fin (n.len + 1)) j w)
    (pdTermCoefficientMap_unit p A B r n.len a)

private theorem coefficient_zero_f (j : ℕ) (x : (pdDeRhamColumn p A r ⦋0⦌).X j) :
    (pdCompletedColumnCoefficientHom p A B r ⦋0⦌).f j x =
      pdColumnZeroCoefficientAt p A B r j x := rfl

/-- 完備列の係数変更は自由模型の完備化単位と厳密に可換。 -/
theorem pdCompletedColumnCoefficientHom_unit :
    pdColumnCompletionUnit p A r n ≫ pdCompletedColumnCoefficientHom p A B r n =
      pdUncompletedColumnCoefficientHom A B r n ≫
        (R).map (pdColumnCompletionUnit p B r n) :=
  coefficient_unit p A B r n

/-- 第 0 列の係数変更の各成分は、総複体の射影で得た成分と一致する。 -/
theorem pdCompletedColumnCoefficientHom_zero_f (j : ℕ) (x : (pdDeRhamColumn p A r ⦋0⦌).X j) :
    (pdCompletedColumnCoefficientHom p A B r ⦋0⦌).f j x =
      pdColumnZeroCoefficientAt p A B r j x :=
  coefficient_zero_f p A B r j x

end SerrePositivity.BhattScholze.Prismatic
