module

public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Generators
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import Mathlib.RingTheory.Flat.Basic
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.IsTensorProduct

/-! # 根の塔の有限段への有限代数の基底変更

## 概要

有限 `A` 代数 `D` と根の塔の有限段 `A_n` について、基底変更 `D_n = A_n ⊗[A] D`（`StageAlgebra`）とその代数構造を定め、`D_0 ≃ D` を与える。有限段から塔・完備テンソル積への写像（`stageToCompletedTower`・`stageToCompletedTensor`）、`D_n` の有限性・次元・局所性、パラメータ系の取り替え、冪の所属、共通の剰余体での長さの比較を示す。完備塔への基底変更 `C ⊗_{A_n} D_n ≃ C ⊗_A D` を同定し、Noether な基底の上で完備テンソル代数が `D_n` 上平坦であることを示す。

## 方針

有限段の代数構造は塔の段の多項式表示から作る。平坦性は完備塔の段の上の平坦性を押し出しで移す。

## 規約

名前空間は根の塔の慣例どおり `SerrePositivity.Section2`。右因子の代数構造は局所的に指定し、大域的な instance は加えない（`stageAlgebraIsNoetherianOfBase` などの既存の instance を除く）。旧 `CLMST/StageAlgebra`・`StageTensor` の基礎の部分と `StageBaseChange`・`StageFiniteness`・`StageDimension`・`StageLocality`・`StageParameterChange`・`StagePowerMembership`・`StageResidueLength`・`CompletedStageBaseChange`（2a で CLMST から下ろした）。`RPerfd` への写像は CLMST/StageRPerfd。

## 使われ方

CLMST の Cor 4.0.4・Prop 4.0.10・Prop 4.0.14・Claim 4.0.15 の有限段の評価。
-/

@[expose] public noncomputable section

universe u

section StageAlgebraPart

open scoped TensorProduct
open IsLocalRing

namespace SerrePositivity.Section2
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- CLMST の有限段の基底変更 `D_n=A_n⊗_A D`。
独立した型名により、D の右作用を通常のテンソル積の左作用と区別する。 -/
def StageAlgebra (n : ℕ) : Type u := TowerStage A t p n ⊗[A] D

instance stageAlgebraCommRing (n : ℕ) : CommRing (StageAlgebra A D t p n) :=
  inferInstanceAs (CommRing (TowerStage A t p n ⊗[A] D))

instance stageAlgebraBase (n : ℕ) : Algebra A (StageAlgebra A D t p n) :=
  inferInstanceAs (Algebra A (TowerStage A t p n ⊗[A] D))

instance stageAlgebraStage (n : ℕ) : Algebra (TowerStage A t p n) (StageAlgebra A D t p n) :=
  inferInstanceAs (Algebra (TowerStage A t p n) (TowerStage A t p n ⊗[A] D))

instance stageAlgebraD (n : ℕ) : Algebra D (StageAlgebra A D t p n) :=
  Algebra.TensorProduct.rightAlgebra

instance stageAlgebraScalarTowerStage (n : ℕ) :
    IsScalarTower A (TowerStage A t p n) (StageAlgebra A D t p n) :=
  inferInstanceAs (IsScalarTower A (TowerStage A t p n) (TowerStage A t p n ⊗[A] D))

instance stageAlgebraScalarTowerD (n : ℕ) : IsScalarTower A D (StageAlgebra A D t p n) := by
  let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact inferInstanceAs (IsScalarTower A D (TowerStage A t p n ⊗[A] D))

/-- 零段では各根の関係が `X_i=t_i` となるので、基底環へ評価できる。 -/
def stage0ToBase : TowerStage A t p 0 →ₐ[A] A :=
  Ideal.Quotient.liftₐ (towerRel A t p 0) (MvPolynomial.aeval t) (by
    have hker : towerRel A t p 0 ≤ RingHom.ker (MvPolynomial.aeval t).toRingHom := by
      change Ideal.span (Set.range fun i : Fin h ↦
        MvPolynomial.X i ^ (p ^ 0) - MvPolynomial.C (t i)) ≤ _
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    intro f hf
    exact hker hf)

/-- 零段から基底環への写像は、多項式代表元を座標 t で評価する。 -/
@[simp] theorem stage0ToBase_mk (f : MvPolynomial (Fin h) A) :
    stage0ToBase A t p (Ideal.Quotient.mk (towerRel A t p 0) f) = MvPolynomial.aeval t f := rfl

/-- 根の塔の零段は、基底環 A と A 代数として同型。素数性や局所性は不要。 -/
def stage0BaseEquiv : TowerStage A t p 0 ≃ₐ[A] A := by
  refine AlgEquiv.ofAlgHom (stage0ToBase A t p) (Algebra.ofId A (TowerStage A t p 0)) ?_ ?_
  · ext
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
      stage0ToBase_mk, MvPolynomial.aeval_X]
    change algebraMap A (TowerStage A t p 0) (t i) =
      Ideal.Quotient.mk (towerRel A t p 0) (MvPolynomial.X i)
    simpa only [pow_zero, pow_one] using (mk_X_pow A t p 0 i).symm

/-- `D_0=A_0⊗_A D` と D の、標準的な D 代数同型。 -/
def stage0Equiv : StageAlgebra A D t p 0 ≃ₐ[D] D := by
  letI : Algebra D (TowerStage A t p 0 ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.commRight A D (TowerStage A t p 0)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[D] D) (stage0BaseEquiv A t p)).trans
      (Algebra.TensorProduct.rid A D D))

/-- 零段同型は D の標準的な像を元へ戻す。 -/
@[simp] theorem stage0Equiv_algebraMap (d : D) :
    stage0Equiv A D t p (algebraMap D (StageAlgebra A D t p 0) d) = d :=
  (stage0Equiv A D t p).commutes d

/-- 零段への D の標準写像は単射。 -/
theorem stage0_algebraMap_injective :
    Function.Injective (algebraMap D (StageAlgebra A D t p 0)) := by
  intro x y hxy
  simpa using congrArg (stage0Equiv A D t p) hxy

/-- 零段への D の標準写像は全射。 -/
theorem stage0_algebraMap_surjective :
    Function.Surjective (algebraMap D (StageAlgebra A D t p 0)) := by
  intro x
  refine ⟨stage0Equiv A D t p x, ?_⟩
  apply (stage0Equiv A D t p).injective
  simp

instance stage0ModuleFinite : Module.Finite D (StageAlgebra A D t p 0) :=
  Module.Finite.of_surjective (Algebra.linearMap D (StageAlgebra A D t p 0))
    (stage0_algebraMap_surjective A D t p)

instance stage0IsLocalRing [IsLocalRing D] : IsLocalRing (StageAlgebra A D t p 0) := by
  have : Nontrivial (StageAlgebra A D t p 0) :=
    ⟨⟨(stage0Equiv A D t p).symm 0, (stage0Equiv A D t p).symm 1,
      fun h ↦ zero_ne_one ((stage0Equiv A D t p).symm.injective h)⟩⟩
  exact IsLocalRing.of_surjective' (algebraMap D (StageAlgebra A D t p 0))
    (stage0_algebraMap_surjective A D t p)

end SerrePositivity.Section2

end StageAlgebraPart

section StageTensorPart

open scoped TensorProduct
namespace SerrePositivity.Section2
open Section2
variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 有限段から未完備塔・完備塔への標準 A 代数写像。 -/
def stageToCompletedTower (n : ℕ) : TowerStage A t p n →ₐ[A] CompletedTower A t p :=
  (IsScalarTower.toAlgHom A (Tower A t p) (CompletedTower A t p)).comp
    (IsScalarTower.toAlgHom A (TowerStage A t p n) (Tower A t p))

/-- D_n=A_n⊗_A D から A∞⊗_A D への標準 A 代数写像。 -/
def stageToCompletedTensor (n : ℕ) : StageAlgebra A D t p n →ₐ[A]
    (CompletedTower A t p) ⊗[A] D :=
  Algebra.TensorProduct.map (stageToCompletedTower A t p n) (AlgHom.id A D)

@[simp] theorem stageToCompletedTensor_algebraMap (n : ℕ) (a : A) :
    stageToCompletedTensor A D t p n (algebraMap A (StageAlgebra A D t p n) a) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) a :=
  (stageToCompletedTensor A D t p n).commutes a

@[simp] theorem stageToCompletedTensor_tmul (n : ℕ) (a : TowerStage A t p n) (d : D) :
    stageToCompletedTensor A D t p n (a ⊗ₜ[A] d) =
      stageToCompletedTower A t p n a ⊗ₜ[A] d := by
  change Algebra.TensorProduct.map (stageToCompletedTower A t p n) (AlgHom.id A D)
    (a ⊗ₜ[A] d) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

end SerrePositivity.Section2

end StageTensorPart

section StageBaseChangePart

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace SerrePositivity.Section2
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 基底変更した段における、左因子から来る根の座標。 -/
abbrev stageRoot (n : ℕ) (i : Fin h) : StageAlgebra A D t p n :=
  algebraMap (TowerStage A t p n) (StageAlgebra A D t p n)
    (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i))

/-- A 上の根の段から、D 上の対応する根の段への係数変更写像。 -/
def stageMap (n : ℕ) :
    TowerStage A t p n →ₐ[A] TowerStage D (algebraMap A D ∘ t) p n :=
  Ideal.Quotient.liftₐ (towerRel A t p n)
    (MvPolynomial.aeval fun i ↦
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i))
    (relIdeal_apply_eq_zero t (p ^ n) _ (by
      intro i
      rw [MvPolynomial.aeval_X, mk_X_pow]
      exact (IsScalarTower.algebraMap_apply A D
        (TowerStage D (algebraMap A D ∘ t) p n) (t i)).symm))

/-- 係数変更写像は多項式代表元を、対応する D 上の根で評価する。 -/
@[simp] theorem stageMap_mk (n : ℕ) (f : MvPolynomial (Fin h) A) :
    stageMap A D t p n (Ideal.Quotient.mk (towerRel A t p n) f) =
      MvPolynomial.aeval (R := A) (fun i ↦
        Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i)) f := rfl

/-- 係数変更写像は A 上の根の座標を D 上の根の座標へ送る。 -/
@[simp] theorem stageMap_mk_X (n : ℕ) (i : Fin h) :
    stageMap A D t p n (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i) := by
  rw [stageMap_mk, MvPolynomial.aeval_X]

/-- テンソル積の左因子の根を D 上の根へ送る、基底変更の標準写像。 -/
def stageBaseChangeTo (n : ℕ) :
    StageAlgebra A D t p n →ₐ[D] TowerStage D (algebraMap A D ∘ t) p n := by
  letI : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.lift
    (Algebra.ofId D (TowerStage D (algebraMap A D ∘ t) p n))
    (stageMap A D t p n) (fun _ _ ↦ Commute.all _ _)).comp
      (Algebra.TensorProduct.commRight A D (TowerStage A t p n)).symm.toAlgHom

/-- 基底変更の標準写像は、単純テンソルを二つの因子の像の積へ送る。 -/
@[simp] theorem stageBaseChangeTo_tmul (n : ℕ) (x : TowerStage A t p n) (d : D) :
    stageBaseChangeTo A D t p n (x ⊗ₜ[A] d) =
      algebraMap D (TowerStage D (algebraMap A D ∘ t) p n) d * stageMap A D t p n x := rfl

/-- 標準写像は左側の根の座標を、D 上の対応する根へ送る。 -/
@[simp] theorem stageBaseChangeTo_stageRoot (n : ℕ) (i : Fin h) :
    stageBaseChangeTo A D t p n (stageRoot A D t p n i) =
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i) := by
  change stageBaseChangeTo A D t p n
    (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i) ⊗ₜ[A] 1) = _
  simp

/-- D 上の根をテンソル積の左因子の根へ送る、基底変更写像の逆。 -/
def stageBaseChangeInv (n : ℕ) :
    TowerStage D (algebraMap A D ∘ t) p n →ₐ[D] StageAlgebra A D t p n :=
  Ideal.Quotient.liftₐ (towerRel D (algebraMap A D ∘ t) p n)
    (MvPolynomial.aeval (stageRoot A D t p n))
    (relIdeal_apply_eq_zero (algebraMap A D ∘ t) (p ^ n) _ (by
      intro i
      rw [MvPolynomial.aeval_X]
      change (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n)
        (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i))) ^ (p ^ n) = _
      rw [← map_pow, mk_X_pow]
      rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (StageAlgebra A D t p n)]
      exact IsScalarTower.algebraMap_apply A D (StageAlgebra A D t p n) (t i)))

/-- 逆写像は D 上の根の座標を、基底変更した段の左側の根へ送る。 -/
@[simp] theorem stageBaseChangeInv_mk_X (n : ℕ) (i : Fin h) :
    stageBaseChangeInv A D t p n
      (Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i)) =
        stageRoot A D t p n i := by
  change MvPolynomial.aeval (stageRoot A D t p n) (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

/-- 係数変更の後に逆写像を適用すると、テンソル積の左因子の標準像となる。 -/
theorem stageBaseChangeInv_stageMap (n : ℕ) (x : TowerStage A t p n) :
    stageBaseChangeInv A D t p n (stageMap A D t p n x) =
      algebraMap (TowerStage A t p n) (StageAlgebra A D t p n) x := by
  have he : ((stageBaseChangeInv A D t p n).restrictScalars A).comp (stageMap A D t p n) =
      IsScalarTower.toAlgHom A (TowerStage A t p n) (StageAlgebra A D t p n) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk,
      stageMap_mk_X, stageBaseChangeInv_mk_X]
    rfl
  exact AlgHom.congr_fun he x

/-- 根の添加は基底変更と両立する。
`A_n⊗_A D` は、D 上で `t_i` の像の根を添加した段と D 代数として同型。 -/
def stageBaseChangeEquiv (n : ℕ) :
    StageAlgebra A D t p n ≃ₐ[D] TowerStage D (algebraMap A D ∘ t) p n := by
  refine AlgEquiv.ofAlgHom (stageBaseChangeTo A D t p n) (stageBaseChangeInv A D t p n) ?_ ?_
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
      stageBaseChangeInv_mk_X, stageBaseChangeTo_stageRoot]
  · apply AlgHom.ext
    intro x
    change TowerStage A t p n ⊗[A] D at x
    induction x using TensorProduct.inductionOn with
    | tmul x d =>
      simp only [AlgHom.comp_apply, AlgHom.id_apply, stageBaseChangeTo_tmul, map_mul,
        AlgHom.commutes, stageBaseChangeInv_stageMap]
      change (1 ⊗ₜ[A] d) * (x ⊗ₜ[A] 1) = x ⊗ₜ[A] d
      simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- 基底変更同型は D の標準的な係数を保つ。 -/
@[simp] theorem stageBaseChangeEquiv_algebraMap_D (n : ℕ) (d : D) :
    stageBaseChangeEquiv A D t p n (algebraMap D (StageAlgebra A D t p n) d) =
      algebraMap D (TowerStage D (algebraMap A D ∘ t) p n) d :=
  (stageBaseChangeEquiv A D t p n).commutes d

/-- 基底変更同型は、根の座標を対応する D 上の根へ送る。 -/
@[simp] theorem stageBaseChangeEquiv_stageRoot (n : ℕ) (i : Fin h) :
    stageBaseChangeEquiv A D t p n (stageRoot A D t p n i) =
      Ideal.Quotient.mk (towerRel D (algebraMap A D ∘ t) p n) (MvPolynomial.X i) :=
  stageBaseChangeTo_stageRoot A D t p n i

end SerrePositivity.Section2

end StageBaseChangePart

section StageFinitenessPart

open scoped TensorProduct
namespace SerrePositivity.Section2
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 零段は D と代数同型なので、D の Noether 性を継承する。素数性は不要。 -/
instance stage0IsNoetherian [IsNoetherianRing D] :
    IsNoetherianRing (StageAlgebra A D t p 0) :=
  isNoetherianRing_of_surjective D (StageAlgebra A D t p 0)
    (algebraMap D (StageAlgebra A D t p 0)) (stage0_algebraMap_surjective A D t p)

variable [Fact p.Prime]

/-- D が A 上有限なら、有限段の基底変更も A 上有限。 -/
instance stageAlgebraFiniteA [Module.Finite A D] (n : ℕ) :
    Module.Finite A (StageAlgebra A D t p n) := by
  have : Module.Finite A (TowerStage A t p n) := towerStage_finite A t p n
  exact inferInstanceAs (Module.Finite A (TowerStage A t p n ⊗[A] D))

/-- 有限段の基底変更は D 上有限。D の A 上の有限性や Noether 性は不要。 -/
instance stageAlgebraFiniteD (n : ℕ) : Module.Finite D (StageAlgebra A D t p n) := by
  have : Module.Finite A (TowerStage A t p n) := towerStage_finite A t p n
  let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let e : (D ⊗[A] TowerStage A t p n) ≃ₐ[D] StageAlgebra A D t p n :=
    Algebra.TensorProduct.commRight A D (TowerStage A t p n)
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- D が Noether 環なら、D 上有限なすべての段も Noether 環。 -/
instance stageAlgebraIsNoetherian [IsNoetherianRing D] (n : ℕ) :
    IsNoetherianRing (StageAlgebra A D t p n) :=
  IsNoetherianRing.of_finite D (StageAlgebra A D t p n)

/-- Noether 基底 A と有限な A 代数 D からも、有限段の Noether 性を供給できる。 -/
instance (priority := 90) stageAlgebraIsNoetherianOfBase
    [IsNoetherianRing A] [Module.Finite A D] (n : ℕ) :
    IsNoetherianRing (StageAlgebra A D t p n) :=
  IsNoetherianRing.of_finite A (StageAlgebra A D t p n)

end SerrePositivity.Section2

end StageFinitenessPart

section StageDimensionPart

open scoped TensorProduct
namespace SerrePositivity.Section2
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 有限段の基底変更の D 上の単項式基底。基底の添字は根の各指数を記録する。 -/
def stageAlgebraBasis (n : ℕ) :
    Module.Basis (Fin h → Fin (p ^ n)) D (StageAlgebra A D t p n) := by
  let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let e : (D ⊗[A] TowerStage A t p n) ≃ₐ[D] StageAlgebra A D t p n :=
    Algebra.TensorProduct.commRight A D (TowerStage A t p n)
  exact ((towerStageBasis A t p n).baseChange D).map e.toLinearEquiv

/-- 各有限段は D 上自由。D が A 上有限であるという仮定は不要。 -/
theorem stageAlgebra_free (n : ℕ) : Module.Free D (StageAlgebra A D t p n) :=
  Module.Free.of_basis (stageAlgebraBasis A D t p n)

/-- D 上の有限段のランクは、長さの正規化係数と同じ p^(nh)。 -/
theorem finrank_stageAlgebra [Nontrivial D] (n : ℕ) :
    Module.finrank D (StageAlgebra A D t p n) = stageRank h p n := by
  rw [Module.finrank_eq_card_basis (stageAlgebraBasis A D t p n),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, stageRank, pow_mul]

/-- D が非零なら、各有限段も非零。非空の単項式基底の元を使う。 -/
theorem stageAlgebra_nontrivial [Nontrivial D] (n : ℕ) :
    Nontrivial (StageAlgebra A D t p n) :=
  nontrivial_of_ne _ _ ((stageAlgebraBasis A D t p n).ne_zero
    (fun _ ↦ ⟨0, pow_pos_of_prime p n⟩))

/-- D から有限段への標準代数写像は単射。自由性と非零性から忠実な作用を得る。 -/
theorem stageAlgebra_algebraMap_injective [Nontrivial D] (n : ℕ) :
    Function.Injective (algebraMap D (StageAlgebra A D t p n)) := by
  let := stageAlgebra_free A D t p n
  let := stageAlgebra_nontrivial A D t p n
  exact FaithfulSMul.algebraMap_injective D (StageAlgebra A D t p n)

/-- 有限段の基底変更は D と同じ Krull 次元を持つ。有限単射整拡大の次元保存による。 -/
theorem ringKrullDim_stageAlgebra [Nontrivial D] (n : ℕ) :
    ringKrullDim (StageAlgebra A D t p n) = ringKrullDim D :=
  ringKrullDim_eq_of_integral_of_injective D (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)

end SerrePositivity.Section2

end StageDimensionPart

section StageLocalityPart

namespace SerrePositivity.Section2
open Section2 IsLocalRing

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    [IsLocalRing D] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 座標の D での像が極大イデアルに入れば、すべての有限段は局所環。 -/
theorem stageAlgebra_isLocalRing (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) : IsLocalRing (StageAlgebra A D t p n) := by
  let : IsLocalRing (TowerStage D (algebraMap A D ∘ t) p n) :=
    isLocalRing_towerStage D (algebraMap A D ∘ t) p htD n
  let e := stageBaseChangeEquiv A D t p n
  have : Nontrivial (StageAlgebra A D t p n) :=
    ⟨⟨e.symm 0, e.symm 1, fun h ↦ zero_ne_one (e.symm.injective h)⟩⟩
  exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective

/-- D のパラメータ系を含む標準基底から、一般段の局所環構造を供給する。
局所性そのものを外部の仮定として受け取る必要はない。 -/
theorem stageAlgebra_isLocalRing_of_parameters
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) (n : ℕ) :
    IsLocalRing (StageAlgebra A D t p n) := by
  apply stageAlgebra_isLocalRing A D t p _ n
  intro i
  rw [← hsop.2]
  exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))

/-- D のパラメータ系は、すべての有限段に標準写像で移せる。
局所性と有限単射性を、いずれも構成から証明して使う。 -/
theorem isSystemOfParameters_stageAlgebra
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) (n : ℕ)
    {r : ℕ} (z : Fin r → D) (hz : IsSystemOfParameters D z) :
    let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    IsSystemOfParameters (StageAlgebra A D t p n)
      (algebraMap D (StageAlgebra A D t p n) ∘ z) := by
  let := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  exact hz.map_finite (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)

end SerrePositivity.Section2

end StageLocalityPart

section StageParameterChangePart

namespace SerrePositivity.Section2
open Section2 IsLocalRing
variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

omit [IsNoetherianRing A] [IsLocalRing D] [Module.Finite A D] in
/-- Dで正則な元は、D上自由な有限段でも正則。 -/
theorem isSMulRegular_stageAlgebra_of_regular_D (n : ℕ) (a : D)
    (ha : IsSMulRegular D a) : IsSMulRegular (StageAlgebra A D t p n)
      (algebraMap D (StageAlgebra A D t p n) a) := by
  let := stageAlgebra_free A D t p n
  exact ha.of_flat

/-- 有限段の任意のパラメータ系を、Dの非単元正則元に合わせて同じ生成イデアルのまま変更。 -/
theorem stage_parameter_change_of_regular_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ y' : Fin (r + 1) → StageAlgebra A D t p n,
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (algebraMap D (StageAlgebra A D t p n) a)) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  have hm := maximalIdeal_map_le_of_finite_of_injective D (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)
  have haStage : algebraMap D (StageAlgebra A D t p n) a ∈ maximalIdeal (StageAlgebra A D t p n) :=
    hm (Ideal.mem_map_of_mem (algebraMap D (StageAlgebra A D t p n)) haM)
  exact exists_same_span_with_regular_last y hy _ haStage
    (isSMulRegular_stageAlgebra_of_regular_D A D t p n a ha)

/-- 零化冪として正の指数を選べば、その冪についても同じパラメータ変更を適用できる。 -/
theorem stage_parameter_change_of_regular_D_pow
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a)
    (N : ℕ) (hN : 0 < N) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ y' : Fin (r + 1) → StageAlgebra A D t p n,
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') ((algebraMap D (StageAlgebra A D t p n) a) ^ N)) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  simpa only [map_pow] using stage_parameter_change_of_regular_D A D t p htD n
    (a ^ N) (Ideal.pow_mem_of_mem _ haM N hN) (ha.pow N) y hy

/-- 有限段の列の変更と最後の正の冪の選択を、同じ生成イデアルの保存とともに供給する。 -/
theorem stage_parameter_power_selection_of_regular_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
        y' (Fin.last r) ^ k ∈ Ideal.span (Set.range (Fin.init y')) ⊔
          Ideal.span {algebraMap D (StageAlgebra A D t p n) a} := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  have hm := maximalIdeal_map_le_of_finite_of_injective D (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)
  exact exists_same_span_parameters_with_last_pow_mem y hy _
    (hm (Ideal.mem_map_of_mem (algebraMap D (StageAlgebra A D t p n)) haM))
    (isSMulRegular_stageAlgebra_of_regular_D A D t p n a ha)

end SerrePositivity.Section2

end StageParameterChangePart

section StagePowerMembershipPart

open scoped TensorProduct
namespace SerrePositivity.Section2
open Section2 IsLocalRing

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 有限段における D の係数の標準像は、完備テンソル代数の右因子の標準像へ送られる。 -/
@[simp] theorem stageToCompletedTensor_algebraMap_D (n : ℕ) (a : D) :
    stageToCompletedTensor A D t p n (algebraMap D (StageAlgebra A D t p n) a) =
      (1 : CompletedTower A t p) ⊗ₜ[A] a := by
  change stageToCompletedTensor A D t p n ((1 : TowerStage A t p n) ⊗ₜ[A] a) = _
  rw [stageToCompletedTensor_tmul, map_one]

/-- 基底環の係数を D と有限段を経由して移しても、完備テンソル代数の標準係数に一致する。 -/
@[simp] theorem stageToCompletedTensor_algebraMap_D_base (n : ℕ) (g : A) :
    stageToCompletedTensor A D t p n
      (algebraMap D (StageAlgebra A D t p n) (algebraMap A D g)) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) g := by
  rw [← IsScalarTower.algebraMap_apply A D (StageAlgebra A D t p n),
    stageToCompletedTensor_algebraMap]

variable [IsNoetherianRing A] [IsLocalRing D] [Module.Finite A D] [Fact p.Prime]

/-- 正の零化指数 N に合わせて有限段の列を変更し、最後の元の正の冪の所属を
完備テンソル代数へ輸送する。元の生成イデアルを保ち、変更後の冪付き列もパラメータ系。 -/
theorem stage_parameter_power_selection_completed_of_regular_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a)
    (N : ℕ) (hN : 0 < N) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
        stageToCompletedTensor A D t p n
          ((Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) (Fin.last r)) ∈
            Ideal.span (Set.range (stageToCompletedTensor A D t p n ∘ Fin.init y')) ⊔
              Ideal.span {(stageToCompletedTensor A D t p n
                (algebraMap D (StageAlgebra A D t p n) a)) ^ N} := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  obtain ⟨y', k, hspan, hk, hparams, hmem⟩ :=
    stage_parameter_power_selection_of_regular_D A D t p htD n (a ^ N)
      (Ideal.pow_mem_of_mem _ haM N hN) (ha.pow N) y hy
  refine ⟨y', k, hspan, hk, hparams, ?_⟩
  have hmapped := Ideal.mem_map_of_mem (stageToCompletedTensor A D t p n).toRingHom hmem
  simpa only [Fin.snoc_last, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    ← Set.range_comp, map_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hmapped

/-- 基底環の元 g の D 内の像が非単元正則なら、変更後の最後の元の冪は、
完備テンソル代数で先頭列の像と g^N の標準像が生成するイデアルに属する。 -/
theorem stage_parameter_power_selection_completed_of_regular_base
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (g : A) (hgM : algebraMap A D g ∈ maximalIdeal D)
    (hg : IsSMulRegular D (algebraMap A D g)) (N : ℕ) (hN : 0 < N) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
        stageToCompletedTensor A D t p n
          ((Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) (Fin.last r)) ∈
            Ideal.span (Set.range (stageToCompletedTensor A D t p n ∘ Fin.init y')) ⊔
              Ideal.span {(algebraMap A ((CompletedTower A t p) ⊗[A] D) g) ^ N} := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  simpa only [stageToCompletedTensor_algebraMap_D_base] using
    stage_parameter_power_selection_completed_of_regular_D A D t p htD n
      (algebraMap A D g) hgM hg N hN y hy

end SerrePositivity.Section2

end StagePowerMembershipPart

section StageResidueLengthPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.Section2
open Section2 IsLocalRing CategoryTheory

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D] [IsLocalRing D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- D から基底変更した任意の有限段 D_n の剰余体への合成は全射。
D 上の根の段へ移し、その具体的な剰余体の記述を使う。 -/
theorem residue_surjective_stageAlgebra_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D) (n : ℕ) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    Function.Surjective ((residue (StageAlgebra A D t p n)).comp
      (algebraMap D (StageAlgebra A D t p n))) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  let := isLocalRing_towerStage D (algebraMap A D ∘ t) p htD n
  let e := stageBaseChangeEquiv A D t p n
  let : IsLocalHom e.toRingEquiv.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let er := ResidueField.mapEquiv e.toRingEquiv
  have hs := residue_surjective_towerStage D (algebraMap A D ∘ t) p htD n
  dsimp only
  intro x
  obtain ⟨d, hd⟩ := hs (er x)
  refine ⟨d, ?_⟩
  apply er.injective
  change ResidueField.map e.toRingEquiv.toRingHom
      (residue (StageAlgebra A D t p n) (algebraMap D (StageAlgebra A D t p n) d)) = er x
  rw [ResidueField.map_residue]
  change residue (TowerStage D (algebraMap A D ∘ t) p n)
    (e (algebraMap D (StageAlgebra A D t p n) d)) = er x
  rw [e.commutes]
  exact hd

/-- A と D が共通剰余体をもつなら、A から D_n の剰余体への合成も全射。 -/
theorem residue_surjective_stageAlgebra_base
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    Function.Surjective ((residue (StageAlgebra A D t p n)).comp
      (algebraMap A (StageAlgebra A D t p n))) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  have hs := residue_surjective_stageAlgebra_D A D t p htD n
  let := isLocalHom_of_residue_surjective
    (algebraMap D (StageAlgebra A D t p n)) hs
  dsimp only
  intro x
  obtain ⟨d, hd⟩ := hs x
  obtain ⟨a, ha⟩ := hres (residue D d)
  refine ⟨a, ?_⟩
  change residue (StageAlgebra A D t p n) (algebraMap A (StageAlgebra A D t p n) a) = x
  rw [IsScalarTower.algebraMap_apply A D (StageAlgebra A D t p n),
    ← ResidueField.map_residue]
  change residue D (algebraMap A D a) = residue D d at ha
  rw [ha, ResidueField.map_residue]
  exact hd

/-- A_n と D_n の共通剰余体条件。D_n の剰余類を A の元で表し、A_n の定数として選ぶ。 -/
theorem residue_surjective_stageAlgebra_stage
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    Function.Surjective ((residue (StageAlgebra A D t p n)).comp
      (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n))) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro x
  obtain ⟨a, ha⟩ := residue_surjective_stageAlgebra_base A D t p htD hres n x
  refine ⟨algebraMap A (TowerStage A t p n) a, ?_⟩
  change residue (StageAlgebra A D t p n)
    (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n)
      (algebraMap A (TowerStage A t p n) a)) = x
  rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (StageAlgebra A D t p n)]
  exact ha

/-- D_n 加群の長さは A_n へ係数制限しても一致する。無限長の場合も含む。 -/
theorem length_stageAlgebra_eq
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (StageAlgebra A D t p n) M]
    [Module (TowerStage A t p n) M]
    [IsScalarTower (TowerStage A t p n) (StageAlgebra A D t p n) M] :
    Module.length (TowerStage A t p n) M = Module.length (StageAlgebra A D t p n) M := by
  let := stageAlgebra_isLocalRing A D t p htD n
  exact length_eq_of_common_residueField
    (residue_surjective_stageAlgebra_stage A D t p htD hres n) M

/-- ModuleCat の係数制限で表した D_n 加群の長さも、A_n 上と D_n 上で一致する。 -/
theorem length_restrictScalars_stageAlgebra_eq
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D))) (n : ℕ)
    (M : ModuleCat.{u} (StageAlgebra A D t p n)) :
    Module.length (TowerStage A t p n)
      ((ModuleCat.restrictScalars (algebraMap (TowerStage A t p n)
        (StageAlgebra A D t p n))).obj M) = Module.length (StageAlgebra A D t p n) M := by
  let := stageAlgebra_isLocalRing A D t p htD n
  exact length_restrictScalars_eq
    (residue_surjective_stageAlgebra_stage A D t p htD hres n) M

end SerrePositivity.Section2

end StageResidueLengthPart

section CompletedStageBaseChangePart

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace SerrePositivity.Section2
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- テンソル環の構成では、有限段の完備塔上の作用を代数から得られる加群構造で固定する。
このインスタンスの登録は本ファイル内だけに限る。 -/
local instance completedStageModule (n : ℕ) :
    Module (TowerStage A t p n) (CompletedTower A t p) := Algebra.toModule

/-- 有限段で先に基底変更してから完備塔へ移す操作は、基底環からの直接の基底変更と同型。 -/
def completedStageBaseChangeEquiv (n : ℕ) :
    (CompletedTower A t p) ⊗[TowerStage A t p n] (StageAlgebra A D t p n) ≃ₐ[CompletedTower A t p]
      (CompletedTower A t p) ⊗[A] D :=
  Algebra.TensorProduct.cancelBaseChange A (TowerStage A t p n)
    (CompletedTower A t p) (CompletedTower A t p) D

/-- 同型は、三つの因子からなる単純テンソルを標準の積へ送る。 -/
@[simp] theorem completedStageBaseChangeEquiv_tmul (n : ℕ)
    (c : CompletedTower A t p) (b : TowerStage A t p n) (d : D) :
    completedStageBaseChangeEquiv A D t p n (c ⊗ₜ[TowerStage A t p n] (b ⊗ₜ[A] d)) =
      (algebraMap (TowerStage A t p n) (CompletedTower A t p) b * c) ⊗ₜ[A] d := by
  exact Algebra.TensorProduct.cancelBaseChange_tmul _ _ _ _ _ _ _ _

/-- 有限段の右因子を含めてから基底変更同型を適用すると、既存の標準段写像となる。 -/
theorem completedStageBaseChangeEquiv_includeRight_apply (n : ℕ)
    (x : StageAlgebra A D t p n) :
    completedStageBaseChangeEquiv A D t p n
      ((Algebra.TensorProduct.includeRight : StageAlgebra A D t p n →ₐ[TowerStage A t p n]
        (CompletedTower A t p) ⊗[TowerStage A t p n] (StageAlgebra A D t p n)) x) =
      stageToCompletedTensor A D t p n x := by
  change TowerStage A t p n ⊗[A] D at x
  induction x using TensorProduct.inductionOn with
  | tmul b d =>
    change completedStageBaseChangeEquiv A D t p n
      ((1 : CompletedTower A t p) ⊗ₜ[TowerStage A t p n] (b ⊗ₜ[A] d)) = _
    rw [completedStageBaseChangeEquiv_tmul, mul_one, stageToCompletedTensor_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- 右因子の標準写像との両立を環準同型の等式として公開する。 -/
theorem completedStageBaseChangeEquiv_comp_includeRight (n : ℕ) :
    (completedStageBaseChangeEquiv A D t p n).toRingHom.comp
      (Algebra.TensorProduct.includeRight : StageAlgebra A D t p n →ₐ[TowerStage A t p n]
        (CompletedTower A t p) ⊗[TowerStage A t p n] (StageAlgebra A D t p n)).toRingHom =
      (stageToCompletedTensor A D t p n).toRingHom := by
  ext x
  exact completedStageBaseChangeEquiv_includeRight_apply A D t p n x

/-- 完備テンソル代数への有限段の作用は、既存の標準段写像から定める。
利用先で局所インスタンスとして置くための名前付き代数構造。 -/
@[instance_reducible] def completedTensorStageAlgebra (n : ℕ) :
    Algebra (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) :=
  (stageToCompletedTensor A D t p n).toRingHom.toAlgebra

attribute [local instance] completedTensorStageAlgebra

/-- 段の左作用も、テンソル代数の標準の代数構造から得られる加群構造で固定する。 -/
local instance completedTensorBaseStageModule (n : ℕ) :
    Module (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D) := Algebra.toModule

/-- 段のスカラー作用を、同じ標準の代数構造の作用で局所的に固定する。 -/
local instance completedTensorBaseStageSMul (n : ℕ) :
    SMul (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D) :=
  (inferInstance : Algebra (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D)).toSMul

/-- 有限段 B から D_n を経由する作用は、完備塔 C を経由する標準作用と両立する。 -/
theorem completedTensorStageScalarTower (n : ℕ) :
    IsScalarTower (TowerStage A t p n) (StageAlgebra A D t p n)
      ((CompletedTower A t p) ⊗[A] D) := by
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change algebraMap (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D) b =
    stageToCompletedTensor A D t p n
      (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n) b)
  change algebraMap (TowerStage A t p n) (CompletedTower A t p) b ⊗ₜ[A] 1 =
    stageToCompletedTensor A D t p n (b ⊗ₜ[A] 1)
  rw [stageToCompletedTensor_tmul]
  rfl

/-- 完備テンソル代数は、有限段 B の完備塔 C と D_n による標準押し出し。
右因子の作用を、実際の段写像に固定した形で供給する。 -/
theorem completedTensorStageIsPushout (n : ℕ) :
    letI := completedTensorStageScalarTower A D t p n
    Algebra.IsPushout (TowerStage A t p n) (CompletedTower A t p)
      (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) := by
  let := completedTensorStageScalarTower A D t p n
  constructor
  apply IsBaseChange.of_equiv (completedStageBaseChangeEquiv A D t p n).toLinearEquiv
  intro x
  exact completedStageBaseChangeEquiv_includeRight_apply A D t p n x

/-- Noether 基底上では、完備テンソル代数は任意の基底変更した有限段 D_n 上で平坦。
D の有限性は不要であり、完備塔の B 上の平坦性を押し出しで移す。 -/
theorem flat_completedTensor_over_stage [IsNoetherianRing A] [Fact p.Prime] (n : ℕ) :
    Module.Flat (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) := by
  let := completedTensorStageScalarTower A D t p n
  let := completedTensorStageIsPushout A D t p n
  let := flat_completedTower_over_stage A t p n
  let : Algebra.IsPushout (TowerStage A t p n) (StageAlgebra A D t p n) (CompletedTower A t p)
      ((CompletedTower A t p) ⊗[A] D) := Algebra.IsPushout.symm inferInstance
  exact Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv (TowerStage A t p n)
    (StageAlgebra A D t p n) (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)).symm.toLinearEquiv

end SerrePositivity.Section2

end CompletedStageBaseChangePart
