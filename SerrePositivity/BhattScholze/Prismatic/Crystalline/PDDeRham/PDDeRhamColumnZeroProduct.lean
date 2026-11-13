module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamAxisProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamAxisProduct
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
public import SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
import all SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives

/-!
# 第 0 pd de Rham 列の同型と外積

## 概要
第 0 列と通常の多項式 de Rham 複体の同型が外積を保つことを示す。

## 方針
差変数が空なので分冪因子は係数環。頂点の一次形式は変数の持ち上げで同定する。

## 規約
係数は標数 p で、完備化単位は同型。

## 使われ方
pd de Rham のコホモロジー積。
-/

public noncomputable section

open CategoryTheory DividedPowerAlgebra SerrePositivity.DeRham
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (k : Type u) [CommRing k] (r : ℕ)

local notation "D" => DividedPowerAlgebra k ((Fin r × Fin 0) →₀ k)
local notation "S" => pdRaw k r 0
local notation "T" => Vars k r
local notation "P" => Poly k T

private theorem noDifferenceCoefficients_one : noDifferenceCoefficients k r (1 : D) = 1 := by
  let e := freeDPBasis (Fin r × Fin 0) k
  have h : e 0 = (1 : D) := by simp [e, freeDPMonomial]
  change Finsupp.uniqueLinearEquiv k k 0 (e.repr 1) = 1
  rw [← h, Module.Basis.repr_self]
  simp

private theorem zeroTermCoefficients_tmul_one (f : MvPolynomial (Fin r) k) :
    zeroTermCoefficients k r (f ⊗ₜ[k] (1 : D)) = MvPolynomial.rename ULift.up f := by
  simp [zeroTermCoefficients, TensorProduct.congr_tmul, noDifferenceCoefficients_one]

private theorem zeroTermCoefficients_mul (x y : S) :
    zeroTermCoefficients k r (x * y) = zeroTermCoefficients k r x * zeroTermCoefficients k r y := by
  have h (z : S) : ∃ f : MvPolynomial (Fin r) k, z = f ⊗ₜ[k] (1 : D) := by
    let e := MvPolynomial.renameEquiv k (Equiv.ulift.symm : Fin r ≃ T)
    refine ⟨e.symm (zeroTermCoefficients k r z), (zeroTermCoefficients k r).injective ?_⟩
    rw [zeroTermCoefficients_tmul_one]
    exact (e.apply_symm_apply _).symm
  obtain ⟨f, rfl⟩ := h x
  obtain ⟨g, rfl⟩ := h y
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, zeroTermCoefficients_tmul_one,
    zeroTermCoefficients_tmul_one, zeroTermCoefficients_tmul_one, map_mul]

variable (p : ℕ) (hp : (p : k) = 0)

private theorem columnZeroIso_tmul (i : ℕ) (f : pdTerm p k r 0)
    (w : ⋀[k]^i (CopyModule k r ⦋0⦌)) :
    (pdDeRhamColumnZeroIso k r p hp).hom.f i (f ⊗ₜ[k] w) =
      deRhamTerm k T i
        (zeroTermCoefficients k r ((pdRawToTerm p k r hp 0).symm f) ⊗ₜ[k]
          zeroExteriorEquiv k r i w) := by
  change zeroFormsEquiv k r i ((pdRawFormsEquiv p k r hp ⦋0⦌ i).symm (f ⊗ₜ[k] w)) = _
  let E := pdRawFormsEquiv p k r hp ⦋0⦌ i
  have h : E.symm (f ⊗ₜ[k] w) = (pdRawToTerm p k r hp 0).symm f ⊗ₜ[k] w := by
    apply E.injective
    erw [E.apply_symm_apply]
  erw [h, zeroFormsEquiv, TensorProduct.congr_tmul]

set_option maxHeartbeats 1000000 in
-- 完備係数と外冪のテンソル表示で型を照合する。
set_option backward.isDefEq.respectTransparency false in
/-- 第 0 列の比較同型は余鎖外積を保つ。 -/
theorem pdDeRhamColumnZeroIso_mul (i j : ℕ) (x : (pdDeRhamColumn p k r ⦋0⦌).X i)
    (y : (pdDeRhamColumn p k r ⦋0⦌).X j) :
    (pdDeRhamColumnZeroIso k r p hp).hom.f (i+j) ((pdColumnCochainProduct p k r 0).mul i j x y) =
      (deRhamCochainWedge k (formVars.{u} r)).mul i j ((pdDeRhamColumnZeroIso k r p hp).hom.f i x)
        ((pdDeRhamColumnZeroIso k r p hp).hom.f j y) := by
  let F (a : ℕ) := (pdDeRhamColumnZeroIso k r p hp).hom.f a
  let L := ((pdColumnCochainProduct p k r 0).mul i j).compr₂ (F (i+j)).hom
  let R := ((deRhamCochainWedge k T).mul i j).compl₁₂ (F i).hom (F j).hom
  have h : L = R := by
    apply TensorProduct.ext'
    intro f v
    apply TensorProduct.ext'
    intro g w
    dsimp only [L, R, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    change F (i+j) (wedgeTensor p k r ⦋0⦌ i j (f ⊗ₜ[k] v) (g ⊗ₜ[k] w)) =
      wedge k T (F i (f ⊗ₜ[k] v)) (F j (g ⊗ₜ[k] w))
    change pdTerm p k r 0 at f g
    change ⋀[k]^i (CopyModule k r ⦋0⦌) at v
    change ⋀[k]^j (CopyModule k r ⦋0⦌) at w
    have hm : wedgeTensor p k r ⦋0⦌ i j (f ⊗ₜ[k] v) (g ⊗ₜ[k] w) =
        (f*g) ⊗ₜ[k] exteriorWedge k (CopyModule k r ⦋0⦌) i j v w := by
      rw [wedgeTensor, TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul, LinearMap.mul_apply']
    erw [hm]
    dsimp only [F]
    rw [columnZeroIso_tmul k r p hp (i+j) (f*g) (exteriorWedge k (CopyModule k r ⦋0⦌) i j v w),
      columnZeroIso_tmul k r p hp i f v, columnZeroIso_tmul k r p hp j g w]
    simp only [deRhamTerm]
    erw [wedge_tmul, map_mul, zeroTermCoefficients_mul]
    let fg : P := zeroTermCoefficients k r ((pdRawToTerm p k r hp 0).symm f) *
      zeroTermCoefficients k r ((pdRawToTerm p k r hp 0).symm g)
    exact congrArg (fun z : ⋀[k]^(i+j) (T → k) => fg ⊗ₜ[k] z)
      (exteriorWedge_map k r ⦋0⦌ (zeroCopyEquiv k r).toLinearMap v w)
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end SerrePositivity.BhattScholze.Prismatic
