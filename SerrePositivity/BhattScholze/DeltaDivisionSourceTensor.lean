module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceAlgebras
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 実自由δ射の通常テンソル積とraw δ包

源Pと終域Lは同じ underlying 型だが、LのP代数構造はα:x↦d zによるもの。
通常テンソル積の標準写像を保つ比較を構成し、導来テンソルの離散性とは区別する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => c
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "B₀" => DeltaAdjoinDivision D d a₀
local notation "j₀" => deltaAdjoinDivisionMap D d a₀
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal d a₀))

/-- raw包の源P代数構造は、基底射jと評価βの合成で与える。 -/
@[instance_reducible] def deltaDivisionSourceRawAlgebra : Algebra P₀ B₀ :=
  ((j₀).comp β₀).toAlgebra

/-- raw包の源作用は、βで作用するAを経由する。 -/
theorem deltaDivisionSourceRawTower :
    let := deltaDivisionSourceEvaluationAlgebra D c
    let := deltaDivisionSourceRawAlgebra (σ := σ) D d c
    let : Module P₀ B₀ := Algebra.toModule
    @IsScalarTower P₀ A B₀
      (deltaDivisionSourceEvaluationAlgebra D c).toSMul
      (inferInstance : Algebra A B₀).toSMul
      (deltaDivisionSourceRawAlgebra (σ := σ) D d c).toSMul := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  let : Module P₀ B₀ := Algebra.toModule
  exact IsScalarTower.of_algebraMap_eq (R := P₀) (S := A) (A := B₀) (fun _ => rfl)

/-- raw標準商射を源P上の代数射として表す。 -/
def deltaDivisionSourceRawRight :
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra (σ := σ) D d c
    letI : Module P₀ B₀ := Algebra.toModule
    P₀ →ₐ[P₀] B₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  letI : Module P₀ B₀ := Algebra.toModule
  exact
    { __ := q₀
      commutes' := fun r => RingHom.congr_fun (deltaDivisionSource_raw_square D d a₀) r }

/-- 通常テンソル積からraw包への実標準環射。 -/
def deltaDivisionSourceTensorToRaw :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ →+* B₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  letI : Module P₀ B₀ := Algebra.toModule
  letI := deltaDivisionSourceRawTower (σ := σ) D d c
  exact (Algebra.TensorProduct.lift (R := P₀) (Algebra.ofId A B₀)
    (deltaDivisionSourceRawRight D d c) (fun _ _ => Commute.all _ _)).toRingHom

/-- テンソルの純元の像は、既存基底射と既存商射の積。 -/
theorem deltaDivisionSourceTensorToRaw_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    deltaDivisionSourceTensorToRaw D d c (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  let : Module P₀ B₀ := Algebra.toModule
  let := deltaDivisionSourceRawTower (σ := σ) D d c
  exact Algebra.TensorProduct.lift_tmul (Algebra.ofId A B₀)
    (deltaDivisionSourceRawRight D d c) (fun _ _ => Commute.all _ _) a b

/-- 通常テンソルの両因子の包含を保つ、raw包からの環射は一意に存在する。 -/
theorem existsUnique_deltaDivisionRawTensorMap :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : B₀ →+* A ⊗[P₀] P₀,
      k.comp q₀ = Algebra.TensorProduct.includeRight.toRingHom ∧
      k.comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  apply existsUnique_deltaDivisionSourceRawLift D d a₀
  exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := P₀) (A := A)
    (B := P₀)).symm

/-- raw包から通常テンソルへの実標準環射。 -/
def deltaDivisionSourceRawToTensor :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    B₀ →+* A ⊗[P₀] P₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  exact Classical.choose (existsUnique_deltaDivisionRawTensorMap (σ := σ) D d c)

/-- rawからテンソルへの射は、元の終域Lの標準像を右因子へ送る。 -/
theorem deltaDivisionSourceRawToTensor_comp_quotient :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceRawToTensor D d c).comp q₀ =
      Algebra.TensorProduct.includeRight.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact (Classical.choose_spec (existsUnique_deltaDivisionRawTensorMap (σ := σ) D d c)).1.1

/-- rawからテンソルへの射は、元の基底Aの標準像を左因子へ送る。 -/
theorem deltaDivisionSourceRawToTensor_comp_base :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceRawToTensor D d c).comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact (Classical.choose_spec (existsUnique_deltaDivisionRawTensorMap (σ := σ) D d c)).1.2

/-- 実通常テンソル積A⊗_P Lは、既存のraw δ除算包と標準的に環同型。 -/
def deltaDivisionSourceTensorEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* B₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  apply RingEquiv.ofRingHom (deltaDivisionSourceTensorToRaw D d c)
    (deltaDivisionSourceRawToTensor D d c)
  · apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    have h := RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_quotient (σ := σ) D d c) r
    change deltaDivisionSourceRawToTensor D d c (q₀ r) = 1 ⊗ₜ[P₀] r at h
    change deltaDivisionSourceTensorToRaw D d c (deltaDivisionSourceRawToTensor D d c (q₀ r)) = q₀ r
    rw [h, deltaDivisionSourceTensorToRaw_tmul, map_one, one_mul]
  · apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro a
      have h := RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_base (σ := σ) D d c) a
      change deltaDivisionSourceRawToTensor D d c (j₀ a) = a ⊗ₜ[P₀] 1 at h
      change deltaDivisionSourceRawToTensor D d c
        (deltaDivisionSourceTensorToRaw D d c (a ⊗ₜ[P₀] 1)) =
        a ⊗ₜ[P₀] 1
      rw [deltaDivisionSourceTensorToRaw_tmul, map_one, mul_one, h]
    · apply RingHom.ext
      intro r
      have h := RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_quotient (σ := σ) D d c) r
      change deltaDivisionSourceRawToTensor D d c (q₀ r) = 1 ⊗ₜ[P₀] r at h
      change deltaDivisionSourceRawToTensor D d c
        (deltaDivisionSourceTensorToRaw D d c (1 ⊗ₜ[P₀] r)) =
        1 ⊗ₜ[P₀] r
      rw [deltaDivisionSourceTensorToRaw_tmul, map_one, one_mul, h]

/-- 通常テンソル比較同型の純元上の具体的な式。 -/
theorem deltaDivisionSourceTensorEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    deltaDivisionSourceTensorEquiv D d c (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact deltaDivisionSourceTensorToRaw_tmul D d c a b

/-- 通常テンソル比較同型の逆は、raw標準商元を右因子の標準像へ送る。 -/
theorem deltaDivisionSourceTensorEquiv_symm_quotient (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceTensorEquiv D d c).symm (q₀ r) = 1 ⊗ₜ[P₀] r := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_quotient (σ := σ) D d c) r

/-- 通常pushout比較は、元の係数Aの標準作用を保つ代数同型。 -/
def deltaDivisionSourceTensorAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃ₐ[A] B₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv D d c)
  intro x
  change deltaDivisionSourceTensorEquiv D d c (x ⊗ₜ[P₀] 1) = j₀ x
  rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one]

end SerrePositivity.BhattScholze
