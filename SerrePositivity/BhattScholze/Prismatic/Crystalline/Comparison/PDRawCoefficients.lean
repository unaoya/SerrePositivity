module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 未完備 pd Čech 模型の係数変換

## 概要
頂点差で表示した pd Čech 模型の係数を環の射に沿って移す。

## 方針
多項式因子と自由分冪因子にそれぞれ係数変換を施す。

## 規約
頂点と変数の添字はそのまま保つ。

## 使われ方
整係数の pd 模型と標数 p の模型の比較。
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)

private abbrev PD (K : Type u) [CommRing K] (n : ℕ) :=
  DividedPowerAlgebra K ((Fin r × Fin n) →₀ K)

local notation "ιₗ" => Algebra.TensorProduct.includeLeft
local notation "ιᵣ" => Algebra.TensorProduct.includeRight

/-- 多項式と自由分冪の両方について係数を変換する。 -/
def pdRawCoefficients (n : ℕ) : pdRaw A r n →ₐ[A] pdRaw B r n :=
  Algebra.TensorProduct.lift
    ((ιₗ : MvPolynomial (Fin r) B →ₐ[B] pdRaw B r n).restrictScalars A |>.comp
      (MvPolynomial.mapAlgHom (Algebra.ofId A B)))
    ((ιᵣ : PD r B n →ₐ[B] pdRaw B r n).restrictScalars A |>.comp
      (DividedPowerAlgebra.map B (freeDPCoefficientMap (Fin r × Fin n) A B)))
    (fun _ _ => Commute.all _ _)

private theorem pdRawCoefficients_tmul (n : ℕ) (x : MvPolynomial (Fin r) A) (y : PD r A n) :
    pdRawCoefficients A B r n (x ⊗ₜ[A] y) =
      MvPolynomial.map (algebraMap A B) x ⊗ₜ[B]
        DividedPowerAlgebra.map B (freeDPCoefficientMap (Fin r × Fin n) A B) y := by
  rw [pdRawCoefficients, Algebra.TensorProduct.lift_tmul]
  change (_ ⊗ₜ[B] (1 : PD r B n)) * ((1 : MvPolynomial (Fin r) B) ⊗ₜ[B] _) = _
  simp

private theorem coefficient_vertexDiff (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) :
    freeDPCoefficientMap (Fin r × Fin n.len) A B (vertexDiff A r n j i) =
      vertexDiff B r n j i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [vertexDiff]
  · simp [vertexDiff, freeDPCoefficientMap, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single]

private theorem coefficient_diffMap {m n : SimplexCategory} (θ : m ⟶ n) (x : Diff A r m) :
    freeDPCoefficientMap (Fin r × Fin n.len) A B (diffMap A r θ x) =
      diffMap B r θ (freeDPCoefficientMap (Fin r × Fin m.len) A B x) := by
  let f := (freeDPCoefficientMap (Fin r × Fin n.len) A B).comp (diffMap A r θ)
  let g := (diffMap B r θ).restrictScalars A |>.comp (freeDPCoefficientMap (Fin r × Fin m.len) A B)
  suffices h : f = g from DFunLike.congr_fun h x
  apply (Finsupp.basisSingleOne (R := A)).ext
  rintro ⟨j,i⟩
  change freeDPCoefficientMap _ A B (diffMap A r θ (vertexDiff A r m j i.succ)) =
    diffMap B r θ (freeDPCoefficientMap _ A B (vertexDiff A r m j i.succ))
  rw [coefficient_vertexDiff, diffMap_vertex, diffMap_vertex, map_sub,
    coefficient_vertexDiff, coefficient_vertexDiff]

private theorem pdRawCoefficients_copy (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) :
    pdRawCoefficients A B r n.len (copy A r n j i) = copy B r n j i := by
  rw [copy, copy, map_add]
  change pdRawCoefficients A B r n.len (MvPolynomial.X j ⊗ₜ[A] (1 : PD r A n.len)) +
      pdRawCoefficients A B r n.len
        ((1 : MvPolynomial (Fin r) A) ⊗ₜ[A] DividedPowerAlgebra.dp A 1 (vertexDiff A r n j i)) =
    MvPolynomial.X j ⊗ₜ[B] (1 : PD r B n.len) +
      (1 : MvPolynomial (Fin r) B) ⊗ₜ[B] DividedPowerAlgebra.dp B 1 (vertexDiff B r n j i)
  simp only [pdRawCoefficients_tmul, map_one, MvPolynomial.map_X,
    DividedPowerAlgebra.map_apply_dp, coefficient_vertexDiff]

private theorem pdRawCoefficients_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    (pdRawCoefficients A B r n.len).comp (pdRawMap A r θ) =
      ((pdRawMap B r θ).restrictScalars A).comp (pdRawCoefficients A B r m.len) := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro j
    change pdRawCoefficients A B r n.len (pdRawMap A r θ (baseVar A r m j)) =
      pdRawMap B r θ (pdRawCoefficients A B r m.len (baseVar A r m j))
    have h (k : Type u) [CommRing k] : baseVar k r m j = copy k r m j 0 := by
      simp [copy, vertexDiff]
    rw [h A, pdRawMap_copy, pdRawCoefficients_copy, pdRawCoefficients_copy, pdRawMap_copy]
  · apply DividedPowerAlgebra.algHom_ext
    intro q x
    have h (K : Type u) [CommRing K] (y : Diff K r m) :
        pdRawMap K r θ ((1 : MvPolynomial (Fin r) K) ⊗ₜ[K] DividedPowerAlgebra.dp K q y) =
          (1 : MvPolynomial (Fin r) K) ⊗ₜ[K] DividedPowerAlgebra.dp K q (diffMap K r θ y) := by
      have h' := DFunLike.congr_fun (pdRawMap_right K r θ) (DividedPowerAlgebra.dp K q y)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, DividedPowerAlgebra.map_apply_dp] at h'
      exact h'
    change pdRawCoefficients A B r n.len (pdRawMap A r θ
      ((1 : MvPolynomial (Fin r) A) ⊗ₜ[A] DividedPowerAlgebra.dp A q x)) =
      pdRawMap B r θ (pdRawCoefficients A B r m.len
        ((1 : MvPolynomial (Fin r) A) ⊗ₜ[A] DividedPowerAlgebra.dp A q x))
    simp only [h, pdRawCoefficients_tmul, map_one, DividedPowerAlgebra.map_apply_dp,
      coefficient_diffMap]

/-- 余単体の構造射と係数変換は可換。 -/
def pdRawChange :
    pdRawModel A r ⋙ Under.forget (CommRingCat.of A) ⟶
      pdRawModel B r ⋙ Under.forget (CommRingCat.of B) where
  app n := CommRingCat.ofHom (pdRawCoefficients A B r n.len).toRingHom
  naturality _ _ θ := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (pdRawCoefficients_nat A B r θ)

/-- 多項式単項式と分冪単項式のテンソルが各項の基底をなす。 -/
def pdRawBasis (n : ℕ) :
    Module.Basis ((Fin r →₀ ℕ) × ((Fin r × Fin n) →₀ ℕ)) A (pdRaw A r n) :=
  (MvPolynomial.basisMonomials (Fin r) A).tensorProduct (freeDPBasis (Fin r × Fin n) A)

private theorem pdRawCoefficients_basis (n : ℕ) (m : (Fin r →₀ ℕ) × ((Fin r × Fin n) →₀ ℕ)) :
    pdRawCoefficients A B r n (pdRawBasis A r n m) = pdRawBasis B r n m := by
  rw [pdRawBasis, pdRawBasis, Module.Basis.tensorProduct_apply',
    Module.Basis.tensorProduct_apply', freeDPBasis_apply, freeDPBasis_apply]
  change pdRawCoefficients A B r n (MvPolynomial.monomial m.1 1 ⊗ₜ[A] freeDPMonomial _ A m.2) =
    MvPolynomial.monomial m.1 1 ⊗ₜ[B] freeDPMonomial _ B m.2
  simp only [pdRawCoefficients_tmul, MvPolynomial.map_monomial, map_one]
  have h := freeDPBaseChangeMap_monomial (Fin r × Fin n) A B m.2
  change algebraMap B _ 1 * DividedPowerAlgebra.map B (freeDPCoefficientMap _ A B)
    (freeDPMonomial _ A m.2) = _ at h
  rw [map_one, one_mul] at h
  rw [h]

/-- 単項式基底の座標では係数変換を座標ごとに行う。 -/
theorem pdRawCoefficients_repr (n : ℕ) (x : pdRaw A r n) :
    (pdRawBasis B r n).repr (pdRawCoefficients A B r n x) =
      freeDPCoefficientMap _ A B ((pdRawBasis A r n).repr x) := by
  let f := ((pdRawBasis B r n).repr.toLinearMap.restrictScalars A).comp
    (pdRawCoefficients A B r n).toLinearMap
  let g := (freeDPCoefficientMap _ A B).comp (pdRawBasis A r n).repr.toLinearMap
  suffices h : f = g from DFunLike.congr_fun h x
  apply (pdRawBasis A r n).ext
  intro m
  change (pdRawBasis B r n).repr (pdRawCoefficients A B r n (pdRawBasis A r n m)) =
    freeDPCoefficientMap _ A B ((pdRawBasis A r n).repr (pdRawBasis A r n m))
  rw [pdRawCoefficients_basis, Module.Basis.repr_self, Module.Basis.repr_self]
  simp [freeDPCoefficientMap, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single]

end SerrePositivity.BhattScholze.Prismatic
