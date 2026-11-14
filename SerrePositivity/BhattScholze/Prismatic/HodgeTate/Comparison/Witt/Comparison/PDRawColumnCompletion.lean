module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 分冪 de Rham 列の自由模型と完備化単位

## 概要
未完備の分冪 de Rham 列を任意の基底環で作り、完備列への標準写像を与える。

## 方針
偏微分の可換性と外積の反可換性で微分の平方を消す。
完備化の単位が偏微分を保つことを純テンソルで確認する。

## 規約
余単体次数を固定し、次数の添字は自然数とする。

## 使われ方
BS 著者版 Theorem 6.4 の有限枠の導来完備底変換に自由模型を使う。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham SerrePositivity.DerivedCompletion
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (n : SimplexCategory)

omit p in
/-- 未完備の分冪微分を二回適用すると零。 -/
theorem pdUncompletedVertical_sq (j : ℕ) :
    (pdRawVertical k r n (j + 1)).comp (pdRawVertical k r n j) = 0 := by
  apply TensorProduct.ext'
  intro f α
  change (pdRawVertical k r n (j + 1))
    (pdRawVertical k r n j (f ⊗ₜ[k] α)) = 0
  simp only [pdRawVertical, LinearMap.sum_apply, TensorProduct.map_tmul, map_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (by simp) (by simp)
  · rintro ⟨a,b⟩
    dsimp
    rw [pdRawPartial_comm k r n.len b a, ← TensorProduct.tmul_add]
    unfold pdCoordinateOne
    rw [wedgeOne_swap, TensorProduct.tmul_zero]
  · rintro ⟨a,b⟩ h he
    have hab : b = a := congrArg Prod.fst he
    subst b
    apply h
    unfold pdCoordinateOne
    rw [wedgeOne_sq, TensorProduct.tmul_zero]

/-- 標数を仮定せず作った未完備分冪 de Rham 列。 -/
@[expose] def pdUncompletedColumn : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun j => ModuleCat.of k (pdRawForms k r n j))
    (fun j => ModuleCat.ofHom (pdRawVertical k r n j))
    (fun j => ModuleCat.hom_ext (pdUncompletedVertical_sq k r n j))

local notation "T" => pdTerm p k r n.len
local notation "R" => pdRaw k r n.len
local notation "M" => ((Fin r × Fin (n.len + 1)) →₀ k)

private def columnUnitCoeff : R →ₗ[k] T :=
  let U := principalCompletionRingCatUnit p (CommRingCat.of R)
  let F : R →ₐ[k] T := ⟨U.hom, fun _ => rfl⟩
  F.toLinearMap

private theorem columnUnitCoeff_partial (a : pdCoordinates r n.len) (x : R) :
    pdPartial p k r n.len a (columnUnitCoeff p k r n x) =
      columnUnitCoeff p k r n (pdRawPartial k r n.len a x) := by
  let U := principalCompletionRingCatUnit p (CommRingCat.of R)
  change principalCompletionLinearMap k p (pdRawPartial k r n.len a) (U x) =
    U (pdRawPartial k r n.len a x)
  exact principalCompletionLinearMap_unit k p (A := R) (B := R) (pdRawPartial k r n.len a) x

/-- 分冪 de Rham 列の完備化単位。 -/
def pdColumnCompletionUnit : pdUncompletedColumn k r n ⟶ pdDeRhamColumn p k r n :=
  CochainComplex.ofHom
    (fun j => ModuleCat.ofHom (TensorProduct.map (columnUnitCoeff p k r n)
      (LinearMap.id : (⋀[k]^j M) →ₗ[k] (⋀[k]^j M)))) (by
      intro j
      rw [column_d_eq]
      dsimp only [pdUncompletedColumn]
      rw [CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a x
      change (∑ t : pdCoordinates r n.len, TensorProduct.map (pdPartial p k r n.len t)
          (wedgeOne k M j (pdCoordinateOne k r n t)))
            (TensorProduct.map (columnUnitCoeff p k r n) LinearMap.id (a ⊗ₜ[k] x)) =
        TensorProduct.map (columnUnitCoeff p k r n) LinearMap.id
          (pdRawVertical k r n j (a ⊗ₜ[k] x))
      simp only [pdRawVertical, LinearMap.sum_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        map_sum, columnUnitCoeff_partial])

omit p in
/-- 未完備分冪形式は基底上自由。 -/
theorem pdRawForms_free (j : ℕ) : Module.Free k (pdRawForms k r n j) := by
  let e := Fintype.equivFin (Fin r × Fin (n.len + 1))
  let : LinearOrder (Fin r × Fin (n.len + 1)) := LinearOrder.lift' e e.injective
  let b : Module.Basis (Fin r × Fin (n.len + 1)) k M := Finsupp.basisSingleOne
  let : Module.Free k (⋀[k]^j M) := Module.Free.of_basis (b.exteriorPower j)
  let : Module.Free k R := Module.Free.of_basis (pdRawBasis k r n.len)
  exact inferInstanceAs (Module.Free k (R ⊗[k] (⋀[k]^j M)))

end SerrePositivity.BhattScholze.Prismatic
