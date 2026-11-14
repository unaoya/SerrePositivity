module

public import SerrePositivity.HomologicalAlgebra.BicomplexRowQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex

/-!
# pd de Rham 総複体から第 0 行への擬同型

## 概要
正の外次数の Čech 行の収縮から第 0 行への射影が擬同型であることを示す。

## 方針
行の収縮をホモロジーの消滅に移し、第一象限の行比較を使う。

## 規約
行の微分は交代余面写像。

## 使われ方
pd Čech 複体と通常の de Rham 複体の比較。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

/-- pd de Rham 総複体から第 0 行への射影は擬同型。 -/
theorem pdDeRhamRowZeroProjection_quasiIso : QuasiIso (pdDeRhamRowZeroProjection p k r) := by
  change QuasiIso (totalToRowZero (pdDeRhamDoubleComplex p k r))
  apply totalToRowZero_quasiIso
  intro a b hb
  change (pdRowComplex p k r b).ExactAt a
  obtain ⟨h⟩ := pdRow_contractible p k r b hb
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero]
    using h.homologyMap_eq a

end SerrePositivity.BhattScholze.Prismatic
