module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionSourceFiniteColimit
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceTensor
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 実自由δ射の通常テンソル積とraw δ包

源Pと終域Lは同じ underlying 型だが、LのP代数構造はα:x↦p zによるもの。
通常テンソル積の標準写像を保つ比較を構成し、導来テンソルの離散性とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal (p : A) a₀))

/-- 終域Lの源P代数構造は、実自由δ射αで与える。 -/
@[instance_reducible] def deltaPDivisionSourceTargetAlgebra : Algebra P₀ P₀ :=
  deltaDivisionSourceTargetAlgebra (σ := σ) D (p : A)

/-- raw包の源P代数構造は、基底射jと評価βの合成で与える。 -/
@[instance_reducible] def deltaPDivisionSourceRawAlgebra : Algebra P₀ B₀ := by
  exact deltaDivisionSourceRawAlgebra D (p : A) a₀

/-- raw包の源作用は、βで作用するAを経由する。 -/
theorem deltaPDivisionSourceRawTower :
    let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    let := deltaPDivisionSourceRawAlgebra (σ := σ) D y
    let : Module P₀ B₀ := Algebra.toModule
    @IsScalarTower P₀ A B₀
      (deltaDivisionSourceEvalAlgebra (σ := σ) D y).toSMul
      (inferInstance : Algebra A B₀).toSMul
      (deltaPDivisionSourceRawAlgebra (σ := σ) D y).toSMul := by
  exact deltaDivisionSourceRawTower D (p : A) a₀

/-- raw標準商射を源P上の代数射として表す。 -/
def deltaPDivisionSourceRawRight :
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := deltaPDivisionSourceRawAlgebra (σ := σ) D y
    letI : Module P₀ B₀ := Algebra.toModule
    P₀ →ₐ[P₀] B₀ := by
  exact deltaDivisionSourceRawRight D (p : A) a₀

/-- 通常テンソル積からraw包への実標準環射。 -/
def deltaPDivisionSourceTensorToRaw :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ →+* B₀ := by
  exact deltaDivisionSourceTensorToRaw D (p : A) a₀

/-- テンソルの純元の像は、既存基底射と既存商射の積。 -/
theorem deltaPDivisionSourceTensorToRaw_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorToRaw D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  exact deltaDivisionSourceTensorToRaw_tmul D (p : A) a₀ a b

/-- 通常テンソルの両因子の包含を保つ、raw包からの環射は一意に存在する。 -/
theorem existsUnique_deltaPDivisionRawTensorMap :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : B₀ →+* A ⊗[P₀] P₀,
      k.comp q₀ = Algebra.TensorProduct.includeRight.toRingHom ∧
      k.comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  exact existsUnique_deltaDivisionRawTensorMap D (p : A) a₀

/-- raw包から通常テンソルへの実標準環射。 -/
def deltaPDivisionSourceRawToTensor :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    B₀ →+* A ⊗[P₀] P₀ := by
  exact deltaDivisionSourceRawToTensor D (p : A) a₀

/-- rawからテンソルへの射は、元の終域Lの標準像を右因子へ送る。 -/
theorem deltaPDivisionSourceRawToTensor_comp_quotient :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceRawToTensor D y).comp q₀ =
      Algebra.TensorProduct.includeRight.toRingHom := by
  exact deltaDivisionSourceRawToTensor_comp_quotient D (p : A) a₀

/-- rawからテンソルへの射は、元の基底Aの標準像を左因子へ送る。 -/
theorem deltaPDivisionSourceRawToTensor_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceRawToTensor D y).comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  exact deltaDivisionSourceRawToTensor_comp_base D (p : A) a₀

/-- 実通常テンソル積A⊗_P Lは、既存のraw δ除算包と標準的に環同型。 -/
def deltaPDivisionSourceTensorEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* B₀ := by
  exact deltaDivisionSourceTensorEquiv D (p : A) a₀

/-- 通常テンソル比較同型の純元上の具体的な式。 -/
theorem deltaPDivisionSourceTensorEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorEquiv D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  exact deltaDivisionSourceTensorEquiv_tmul D (p : A) a₀ a b

/-- 通常テンソル比較同型の逆は、raw標準商元を右因子の標準像へ送る。 -/
theorem deltaPDivisionSourceTensorEquiv_symm_quotient (r : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorEquiv D y).symm (q₀ r) = 1 ⊗ₜ[P₀] r := by
  exact deltaDivisionSourceTensorEquiv_symm_quotient D (p : A) a₀ r


end SerrePositivity.BhattScholze
