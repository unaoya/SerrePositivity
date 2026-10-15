module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceFiniteColimit
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
@[instance_reducible] def deltaPDivisionSourceTargetAlgebra : Algebra P₀ P₀ := (α₀).toAlgebra

/-- raw包の源P代数構造は、基底射jと評価βの合成で与える。 -/
@[instance_reducible] def deltaPDivisionSourceRawAlgebra : Algebra P₀ B₀ :=
  ((j₀).comp β₀).toAlgebra

/-- raw包の源作用は、βで作用するAを経由する。 -/
theorem deltaPDivisionSourceRawTower :
    let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    let := deltaPDivisionSourceRawAlgebra (σ := σ) D y
    let : Module P₀ B₀ := Algebra.toModule
    @IsScalarTower P₀ A B₀
      (deltaDivisionSourceEvalAlgebra (σ := σ) D y).toSMul
      (inferInstance : Algebra A B₀).toSMul
      (deltaPDivisionSourceRawAlgebra (σ := σ) D y).toSMul := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceRawAlgebra (σ := σ) D y
  let : Module P₀ B₀ := Algebra.toModule
  exact IsScalarTower.of_algebraMap_eq (R := P₀) (S := A) (A := B₀) (fun _ => rfl)

/-- raw標準商射を源P上の代数射として表す。 -/
def deltaPDivisionSourceRawRight :
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := deltaPDivisionSourceRawAlgebra (σ := σ) D y
    letI : Module P₀ B₀ := Algebra.toModule
    P₀ →ₐ[P₀] B₀ := by
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaPDivisionSourceRawAlgebra (σ := σ) D y
  letI : Module P₀ B₀ := Algebra.toModule
  exact
    { __ := q₀
      commutes' := fun r => RingHom.congr_fun (deltaDivisionSource_raw_square D (p : A) a₀) r }

/-- 通常テンソル積からraw包への実標準環射。 -/
def deltaPDivisionSourceTensorToRaw :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ →+* B₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaPDivisionSourceRawAlgebra (σ := σ) D y
  letI : Module P₀ B₀ := Algebra.toModule
  letI := deltaPDivisionSourceRawTower (σ := σ) D y
  exact (Algebra.TensorProduct.lift (R := P₀) (Algebra.ofId A B₀)
    (deltaPDivisionSourceRawRight D y) (fun _ _ => Commute.all _ _)).toRingHom

/-- テンソルの純元の像は、既存基底射と既存商射の積。 -/
theorem deltaPDivisionSourceTensorToRaw_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorToRaw D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := deltaPDivisionSourceRawAlgebra (σ := σ) D y
  let : Module P₀ B₀ := Algebra.toModule
  let := deltaPDivisionSourceRawTower (σ := σ) D y
  exact Algebra.TensorProduct.lift_tmul (Algebra.ofId A B₀)
    (deltaPDivisionSourceRawRight D y) (fun _ _ => Commute.all _ _) a b

/-- 通常テンソルの両因子の包含を保つ、raw包からの環射は一意に存在する。 -/
theorem existsUnique_deltaPDivisionRawTensorMap :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : B₀ →+* A ⊗[P₀] P₀,
      k.comp q₀ = Algebra.TensorProduct.includeRight.toRingHom ∧
      k.comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  apply existsUnique_deltaDivisionSourceRawLift D (p : A) a₀
  exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := P₀) (A := A)
    (B := P₀)).symm

/-- raw包から通常テンソルへの実標準環射。 -/
def deltaPDivisionSourceRawToTensor :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    B₀ →+* A ⊗[P₀] P₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact Classical.choose (existsUnique_deltaPDivisionRawTensorMap (σ := σ) D y)

/-- rawからテンソルへの射は、元の終域Lの標準像を右因子へ送る。 -/
theorem deltaPDivisionSourceRawToTensor_comp_quotient :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceRawToTensor D y).comp q₀ =
      Algebra.TensorProduct.includeRight.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  exact (Classical.choose_spec (existsUnique_deltaPDivisionRawTensorMap (σ := σ) D y)).1.1

/-- rawからテンソルへの射は、元の基底Aの標準像を左因子へ送る。 -/
theorem deltaPDivisionSourceRawToTensor_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceRawToTensor D y).comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  exact (Classical.choose_spec (existsUnique_deltaPDivisionRawTensorMap (σ := σ) D y)).1.2

/-- 実通常テンソル積A⊗_P Lは、既存のraw δ除算包と標準的に環同型。 -/
def deltaPDivisionSourceTensorEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* B₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  apply RingEquiv.ofRingHom (deltaPDivisionSourceTensorToRaw D y)
    (deltaPDivisionSourceRawToTensor D y)
  · apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    have h := RingHom.congr_fun (deltaPDivisionSourceRawToTensor_comp_quotient (σ := σ) D y) r
    change deltaPDivisionSourceRawToTensor D y (q₀ r) = 1 ⊗ₜ[P₀] r at h
    change deltaPDivisionSourceTensorToRaw D y (deltaPDivisionSourceRawToTensor D y (q₀ r)) = q₀ r
    rw [h, deltaPDivisionSourceTensorToRaw_tmul, map_one, one_mul]
  · apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro a
      have h := RingHom.congr_fun (deltaPDivisionSourceRawToTensor_comp_base (σ := σ) D y) a
      change deltaPDivisionSourceRawToTensor D y (j₀ a) = a ⊗ₜ[P₀] 1 at h
      change deltaPDivisionSourceRawToTensor D y
        (deltaPDivisionSourceTensorToRaw D y (a ⊗ₜ[P₀] 1)) =
        a ⊗ₜ[P₀] 1
      rw [deltaPDivisionSourceTensorToRaw_tmul, map_one, mul_one, h]
    · apply RingHom.ext
      intro r
      have h := RingHom.congr_fun (deltaPDivisionSourceRawToTensor_comp_quotient (σ := σ) D y) r
      change deltaPDivisionSourceRawToTensor D y (q₀ r) = 1 ⊗ₜ[P₀] r at h
      change deltaPDivisionSourceRawToTensor D y
        (deltaPDivisionSourceTensorToRaw D y (1 ⊗ₜ[P₀] r)) =
        1 ⊗ₜ[P₀] r
      rw [deltaPDivisionSourceTensorToRaw_tmul, map_one, one_mul, h]

/-- 通常テンソル比較同型の純元上の具体的な式。 -/
theorem deltaPDivisionSourceTensorEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    deltaPDivisionSourceTensorEquiv D y (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  exact deltaPDivisionSourceTensorToRaw_tmul D y a b

/-- 通常テンソル比較同型の逆は、raw標準商元を右因子の標準像へ送る。 -/
theorem deltaPDivisionSourceTensorEquiv_symm_quotient (r : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorEquiv D y).symm (q₀ r) = 1 ⊗ₜ[P₀] r := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  exact RingHom.congr_fun (deltaPDivisionSourceRawToTensor_comp_quotient (σ := σ) D y) r

end SerrePositivity.BhattScholze
