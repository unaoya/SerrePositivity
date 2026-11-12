module

public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorPolynomialModule
public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorGrading
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
概要：M⊗_R(R/J) と、既存の閉厚化 M/JM の商係数表示を照合する。
方針：Mathlib のテンソルと商の比較を使い、J の拡大作用の等式で既存の商へ戻す。
規約：J による底変換の平坦性も、H とテンソルの交換も仮定しない。
使われ方：R/J の係数表示と、実際の閉厚化の自然性を共通の加群の射で照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (J : Ideal R)

local instance reesClosedTensorCoefficientModule : Module (R ⧸ J) (M ⊗[R] (R ⧸ J)) :=
  tensorRightCoefficientModule
local instance reesClosedTensorTargetPolynomialModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance reesClosedTensorTargetPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance reesClosedTensorTargetCoefficientModule : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J

/-- 拡大イデアルで定義した一段目の閉厚化は、実際の JM による商。 -/
theorem reesClosedTensor_submodule_eq :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) J 1 = J • (⊤ : Submodule R M) := by
  unfold reesAdicProjectiveSubmodule
  rw [reesExtendedAdic_restrictScalars, pow_one]

/-- 既存の閉厚化と右テンソルの比較。まず元の基底環上で線形に構成する。 -/
def reesClosedTensorEquiv : M ⊗[R] (R ⧸ J) ≃ₗ[R]
    reesAdicProjectiveQuotient (ι := ι) (M := M) J 1 :=
  (TensorProduct.tensorQuotEquivQuotSMul M J).trans
    (Submodule.quotEquivOfEq _ _ (reesClosedTensor_submodule_eq (ι := ι) (M := M) J).symm)

/-- テンソルと閉厚化の比較は、商環の代表を元の係数の作用として計算する。 -/
theorem reesClosedTensorEquiv_tmul_mk (m : M) (r : R) :
    reesClosedTensorEquiv (ι := ι) J (m ⊗ₜ[R] Ideal.Quotient.mk J r) =
      reesAdicProjectiveQuotientProjection (ι := ι) J 1 (r • m) := by
  change (Submodule.quotEquivOfEq _ _
    (reesClosedTensor_submodule_eq (ι := ι) (M := M) J).symm)
      (TensorProduct.tensorQuotEquivQuotSMul M J (m ⊗ₜ[R] Ideal.Quotient.mk J r)) = _
  rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
  rfl

/-- 商係数の作用についても、テンソルと閉厚化の比較は線形。 -/
theorem reesClosedTensorEquiv_smul (b : R ⧸ J) (z : M ⊗[R] (R ⧸ J)) :
    reesClosedTensorEquiv (ι := ι) J (b • z) = b • reesClosedTensorEquiv (ι := ι) J z := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction z using TensorProduct.inductionOn with
  | tmul m c =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [tensorRightCoefficient_smul_tmul, ← map_mul,
      reesClosedTensorEquiv_tmul_mk, reesClosedTensorEquiv_tmul_mk,
      reesClosedCoefficient_mk_smul]
    rw [← (reesAdicProjectiveQuotientProjection (ι := ι) J 1).map_smul_of_tower s]
    congr 1
    exact (smul_smul s r m).symm
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- 既存の R/J 係数の閉厚化との、R/J 線形な同型。 -/
def reesClosedTensorCoefficientEquiv : M ⊗[R] (R ⧸ J) ≃ₗ[R ⧸ J]
    reesAdicProjectiveQuotient (ι := ι) (M := M) J 1 where
  toFun := reesClosedTensorEquiv (ι := ι) J
  invFun := (reesClosedTensorEquiv (ι := ι) (M := M) J).symm
  left_inv := (reesClosedTensorEquiv (ι := ι) (M := M) J).left_inv
  right_inv := (reesClosedTensorEquiv (ι := ι) (M := M) J).right_inv
  map_add' := (reesClosedTensorEquiv (ι := ι) (M := M) J).map_add
  map_smul' := reesClosedTensorEquiv_smul (ι := ι) J

/-- 閉厚化の比較は、元の加群からの射影を保つ。 -/
theorem reesClosedTensorCoefficientEquiv_tmul_one (m : M) :
    reesClosedTensorCoefficientEquiv (ι := ι) J (m ⊗ₜ[R] 1) =
      reesAdicProjectiveQuotientProjection (ι := ι) J 1 m := by
  change reesClosedTensorEquiv (ι := ι) J (m ⊗ₜ[R] 1) = _
  rw [← (Ideal.Quotient.mk J).map_one, reesClosedTensorEquiv_tmul_mk, one_smul]

/-- 商とテンソルの比較は、元の多項式環の作用を保つ。 -/
theorem reesClosedTensorEquiv_polynomial_smul (p : MvPolynomial ι R)
    (z : M ⊗[R] (R ⧸ J)) :
    reesClosedTensorEquiv (ι := ι) J (p • z) = p • reesClosedTensorEquiv (ι := ι) J z := by
  induction z using TensorProduct.inductionOn with
  | tmul m b =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    change reesClosedTensorEquiv (ι := ι) J
      ((p • m) ⊗ₜ[R] Ideal.Quotient.mk J r) = _
    rw [reesClosedTensorEquiv_tmul_mk, reesClosedTensorEquiv_tmul_mk,
      ← (reesAdicProjectiveQuotientProjection (ι := ι) J 1).map_smul]
    congr 1
    exact smul_comm r p m
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

local instance reesClosedTensorSourceNewPolynomialModule :
    Module (MvPolynomial ι (R ⧸ J)) (M ⊗[R] (R ⧸ J)) :=
  projectiveTensorPolynomialModule
local instance reesClosedTensorTargetNewPolynomialModule :
    Module (MvPolynomial ι (R ⧸ J))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J

/-- 既存の閉厚化の多項式係数表示と、テンソルの多項式作用との同型。 -/
def reesClosedTensorPolynomialEquiv : M ⊗[R] (R ⧸ J) ≃ₗ[MvPolynomial ι (R ⧸ J)]
    reesAdicProjectiveQuotient (ι := ι) (M := M) J 1 where
  toFun := reesClosedTensorEquiv (ι := ι) J
  invFun := (reesClosedTensorEquiv (ι := ι) (M := M) J).symm
  left_inv := (reesClosedTensorEquiv (ι := ι) (M := M) J).left_inv
  right_inv := (reesClosedTensorEquiv (ι := ι) (M := M) J).right_inv
  map_add' := (reesClosedTensorEquiv (ι := ι) (M := M) J).map_add
  map_smul' p z := by
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective p
    change reesClosedTensorEquiv (ι := ι) J
      (MvPolynomial.map (algebraMap R (R ⧸ J)) q • z) =
        MvPolynomial.map (Ideal.Quotient.mk J) q • reesClosedTensorEquiv (ι := ι) J z
    rw [projectiveTensorPolynomial_map_smul (R := R) (B := R ⧸ J) (ι := ι) q z,
      reesClosedPolynomialCoefficient_map_smul (ι := ι) J q]
    exact reesClosedTensorEquiv_polynomial_smul J q z

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- 次数成分のテンソル像は、既存の R/J 係数の商次数成分に一致する。 -/
theorem reesClosedTensorPiece_map_eq (d : ℕ) :
    (projectiveTensorPiece (B := R ⧸ J) G d).map
        (reesClosedTensorCoefficientEquiv (ι := ι) J).toLinearMap =
      reesClosedCoefficientPiece (ι := ι) J G d := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := hz
    induction w using TensorProduct.inductionOn with
    | tmul m b =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      change reesClosedTensorEquiv (ι := ι) J
        (m.val ⊗ₜ[R] Ideal.Quotient.mk J r) ∈
        reesAdicProjectiveQuotientPiece (ι := ι) J G 1 d
      rw [reesClosedTensorEquiv_tmul_mk]
      exact reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) J G 1 d _
        ((G d).smul_mem r m.property)
    | add x y hx hy => simpa only [map_add] using
        (reesClosedCoefficientPiece (ι := ι) J G d).add_mem hx hy
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨m ⊗ₜ[R] (1 : R ⧸ J), projectiveTensorPiece_tmul_mem G d m hm 1,
      reesClosedTensorCoefficientEquiv_tmul_one J m⟩

end SerrePositivity.AlgebraicGeometry
