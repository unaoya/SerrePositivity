module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDTor
public import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalFlat
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
import SerrePositivity.CommutativeAlgebra.Module.ScalarTensorView
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# 普遍多項式環上の分冪包の Tor

## 概要
BS 著者版 Lemma 2.38 の ℤ₍ₚ₎ 上の多項式環を基底に取って高次 Tor を計算する。

## 方針
係数環は ℤ₍ₚ₎ 上平坦。自由分冪代数の底変換と Tor の底変換を合わせる。

## 規約
係数環で p は正則、剰余の列は有限 Koszul 正則。

## 使われ方
原典の押し出しの離散性を通常の Tor の消滅として述べる。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

namespace SerrePositivity.BhattScholze

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {r : ℕ}

local notation "P₀" => MvPolynomial (Fin r) R
local notation "P" => MvPolynomial (Fin r) A
local notation "Γ[" B "]" => DividedPowerAlgebra B (Fin r →₀ B)
local notation "γ[" B "," i "]" =>
  DividedPowerAlgebra.dp B 1 (Finsupp.single i 1 : Fin r →₀ B)
local notation "v[" B "]" => (MvPolynomial.aeval (fun i : Fin r => γ[B, i]))
local notation "Γ₀" => Γ[R]
local notation "Γ₁" => Γ[A]

private def freeDPPolynomialTensorEquiv :
    letI : Algebra P₀ Γ₀ := (v[R]).toRingHom.toAlgebra
    letI : Algebra P Γ₁ := (v[A]).toRingHom.toAlgebra
    P ⊗[P₀] Γ₀ ≃ₐ[P] Γ₁ := by
  letI : Algebra P₀ Γ₀ := (v[R]).toRingHom.toAlgebra
  letI : Algebra P Γ₁ := (v[A]).toRingHom.toAlgebra
  let e := freeDPBaseChangeEquiv (Fin r) R A
  let j := (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := Γ₀))
  letI : Algebra Γ₀ Γ₁ := (e.toRingHom.comp j.toRingHom).toAlgebra
  letI : Algebra P₀ Γ₁ := ((algebraMap Γ₀ Γ₁).comp (algebraMap P₀ Γ₀)).toAlgebra
  haveI : IsScalarTower P₀ Γ₀ Γ₁ := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R P₀ Γ₀ := .of_algebraMap_eq fun b => ((v[R]).commutes b).symm
  haveI : IsScalarTower A P Γ₁ := .of_algebraMap_eq fun b => ((v[A]).commutes b).symm
  haveI : IsScalarTower R P Γ₁ := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply R A Γ₁, IsScalarTower.algebraMap_apply R A P,
      IsScalarTower.algebraMap_apply A P Γ₁]
  haveI : IsScalarTower R Γ₀ Γ₁ := IsScalarTower.of_algebraMap_eq
      (R := R) (S := Γ₀) (A := Γ₁) fun b => by
    change algebraMap R Γ₁ b = e (j (algebraMap R Γ₀ b))
    rw [AlgHom.commutes]
    exact (e.toAlgHom.restrictScalars R).commutes b |>.symm
  haveI : IsScalarTower R P₀ Γ₁ := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply R Γ₀ Γ₁, IsScalarTower.algebraMap_apply R P₀ Γ₀]
    rfl
  have h : (algebraMap Γ₀ Γ₁).comp (algebraMap P₀ Γ₀) =
      (algebraMap P Γ₁).comp (algebraMap P₀ P) := by
    apply MvPolynomial.ringHom_ext'
    · simp only [RingHom.comp_assoc, ← MvPolynomial.algebraMap_eq]
      rw [← IsScalarTower.algebraMap_eq R P₀ Γ₀, ← IsScalarTower.algebraMap_eq R Γ₀ Γ₁,
        ← IsScalarTower.algebraMap_eq R P₀ P, ← IsScalarTower.algebraMap_eq R P Γ₁]
    · intro i
      change e (1 ⊗ₜ[R] (v[R]) (MvPolynomial.X i)) =
        (v[A]) (MvPolynomial.map (algebraMap R A) (MvPolynomial.X i))
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X, freeDPBaseChangeEquiv_dp]
  haveI : IsScalarTower P₀ P Γ₁ := .of_algebraMap_eq' h
  have hΓ : Algebra.IsPushout R A Γ₀ Γ₁ :=
    ⟨IsBaseChange.of_equiv e.toLinearEquiv (fun _ => rfl)⟩
  haveI : Algebra.IsPushout P₀ P Γ₀ Γ₁ :=
    ((Algebra.IsPushout.comp_iff (T := Γ₀) (T' := Γ₁) R P₀ A P).mp hΓ.symm).symm
  exact Algebra.IsPushout.equiv P₀ P Γ₀ Γ₁

/-- 概要：普遍多項式環上の通常の押し出しは分冪表示環。
方針：係数を拡大した多項式環を経由し、自由分冪代数の底変換と次数零の表示を合成する。
規約：多項式の二つの脚は各変数を一次分冪と指定係数に送る（BS 著者版 Lemma 2.38）。
使われ方：高次 Tor の消滅と分冪包の普遍性を原典の押し出しで結びつける。 -/
def dpFamilyUniversalTensorEquiv (f : Fin r → A) :
    letI : Algebra P₀ Γ₀ := (v[R]).toRingHom.toAlgebra
    letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
    letI : Algebra P₀ A := ((algebraMap P A).comp (algebraMap P₀ P)).toAlgebra
    A ⊗[P₀] Γ₀ ≃+* DPFamilyPresentation f := by
  letI : Algebra P₀ Γ₀ := (v[R]).toRingHom.toAlgebra
  letI : Algebra P Γ₁ := (v[A]).toRingHom.toAlgebra
  letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra P₀ A := ((algebraMap P A).comp (algebraMap P₀ P)).toAlgebra
  haveI : IsScalarTower P₀ P A := .of_algebraMap_eq fun _ => rfl
  let e₀ := (Algebra.TensorProduct.cancelBaseChange P₀ P A A Γ₀).symm
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
    (freeDPPolynomialTensorEquiv (R := R) (A := A) (r := r))
  let e₂ := Algebra.TensorProduct.comm P A Γ₁
  exact (e₀.trans e₁).toRingEquiv.trans (e₂.toRingEquiv.trans
    (dpFamilyPresentation_polynomialTensorEquiv f).toRingEquiv)

/-- 概要：p 局所整数の多項式環で定めた押し出しの高次 Tor は零。
方針：係数の平坦性により Tor を係数多項式環に移し、分冪表示関係の Koszul 計算を使う。
規約：BS 著者版 Lemma 2.38 の多項式環の二脚。
使われ方：一般の有限 Koszul 正則列の分冪包。 -/
theorem dpFamilyUniversalTor_subsingleton {p : ℕ} [Fact p.Prime] [Algebra (PrimeLocalInt p) A]
    (f : Fin r → A) (hp : IsSMulRegular A (p : A))
    (hf : IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ f)) (i : ℕ) :
    let R₀ := ULift.{u} (PrimeLocalInt p)
    letI : Algebra R₀ A := ((algebraMap (PrimeLocalInt p) A).comp
      (ULift.ringEquiv : R₀ ≃+* PrimeLocalInt p).toRingHom).toAlgebra
    let Pbase := MvPolynomial (Fin r) R₀
    letI : Algebra Pbase (Γ[R₀]) := (v[R₀]).toRingHom.toAlgebra
    letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
    Subsingleton (TorModule Pbase (i + 1)
      ((ModuleCat.restrictScalars (algebraMap Pbase P)).obj (ModuleCat.of P A))
      (Γ[R₀])) := by
  let R₀ := ULift.{u} (PrimeLocalInt p)
  let eR : R₀ ≃+* PrimeLocalInt p := ULift.ringEquiv
  letI : Algebra R₀ A := ((algebraMap (PrimeLocalInt p) A).comp eR.toRingHom).toAlgebra
  let Pbase := MvPolynomial (Fin r) R₀
  let Gbase := Γ[R₀]
  letI : Algebra Pbase Gbase := (v[R₀]).toRingHom.toAlgebra
  letI : Algebra P Γ₁ := (v[A]).toRingHom.toAlgebra
  letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
  have hlocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : A) := by
    simpa only [map_natCast] using (primeLocalInt_isUnit p m hm).map (algebraMap (PrimeLocalInt p) A)
  haveI : Module.Flat (PrimeLocalInt p) A := primeLocalInt_moduleFlat hlocal hp
  letI : Algebra R₀ (PrimeLocalInt p) := eR.toRingHom.toAlgebra
  letI : Module R₀ (PrimeLocalInt p) := Algebra.toModule
  letI : Module R₀ A := Algebra.toModule
  let eLin : R₀ ≃ₗ[R₀] PrimeLocalInt p :=
    { __ := eR.toAddEquiv
      map_smul' := fun x y => eR.map_mul x y }
  haveI : Module.Flat R₀ (PrimeLocalInt p) := Module.Flat.of_linearEquiv eLin.symm
  letI := IsScalarTower.of_algebraMap_eq' (R := R₀) (S := PrimeLocalInt p) (A := A) rfl
  haveI : Module.Flat R₀ A := Module.Flat.trans R₀ (PrimeLocalInt p) A
  haveI : Module.Flat Pbase P :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv R₀ Pbase A P).symm.toLinearEquiv
  let M := ModuleCat.of Pbase Gbase
  let N := ModuleCat.of P A
  let U := ModuleCat.restrictScalars (algebraMap Pbase P)
  let E := ModuleCat.extendScalars (algebraMap Pbase P)
  let e₀ := torAcyclicBaseChangeIso (algebraMap Pbase P) M
    (scalarExtensionTorVanishing_of_flat_algebra M) N (i + 1)
  let e₁ : E.obj M ≃ₗ[P] Γ₁ :=
    (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := P) M).trans
      (freeDPPolynomialTensorEquiv (R := R₀) (A := A) (r := r)).toLinearEquiv
  let e₂ := U.mapIso (((Tor (ModuleCat P) (i+1)).obj N).mapIso e₁.toModuleIso)
  let e₃ := U.mapIso ((torComm (i+1) N (ModuleCat.of P Γ₁)).toModuleIso)
  let e₄ := U.mapIso (torAlgebraComparison (C := Γ₁) N (i+1))
  letI : Subsingleton (U.obj ((ModuleCat.restrictScalars (algebraMap P Γ₁)).obj
      (((ModuleCat.extendScalars (algebraMap P Γ₁)).leftDerived (i+1)).obj N))) :=
    dpFamilyPresentation_tor_subsingleton f hlocal hp hf i
  exact (e₀ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).toLinearEquiv.injective.subsingleton

end SerrePositivity.BhattScholze
