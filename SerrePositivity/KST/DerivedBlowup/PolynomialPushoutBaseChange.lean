module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import SerrePositivity.CommutativeAlgebra.Module.ScalarTensorView

/-!
概要：KST Lemma3.6 の多項式表示環の pushout に沿う加群底変更の標準比較。
方針：Mathlib の IsPushout.cancelBaseChange を ModuleCat の自然同型へ束ねる。
規約：多項式環上の加群を基底へ制限してから底変更する二経路を比較する。
使われ方：普遍基底上の導来 tensor とチャート表示環上の tensor の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {I : Type}

/-- 概要：多項式 pushout の二経路の加群底変更は標準同型。
方針：pushout の tensor 消去同型を係数制限した ModuleCat の型へ合わせる。
規約：KST Lemma3.6。使われ方：複体の各次数の底変更比較。 -/
def polynomialPushoutModuleIso (M : ModuleCat.{u} (MvPolynomial I A)) :
    (ModuleCat.restrictScalars (algebraMap B (MvPolynomial I B))).obj
      ((ModuleCat.extendScalars (algebraMap (MvPolynomial I A) (MvPolynomial I B))).obj M) ≅
    (ModuleCat.extendScalars (algebraMap A B)).obj
      ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).obj M) := by
  letI : Module A M := Module.restrictScalars A (MvPolynomial I A) M
  letI : IsScalarTower A (MvPolynomial I A) M :=
    IsScalarTower.restrictScalars A (MvPolynomial I A) M
  exact
    (ModuleCat.restrictScalars (algebraMap B (MvPolynomial I B))).mapIso
      (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := MvPolynomial I B) M).toModuleIso ≪≫
    (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarRestrictionTensorView (A := B) M).toModuleIso ≪≫
    (Algebra.IsPushout.cancelBaseChange A B (MvPolynomial I A) (MvPolynomial I B) M).toModuleIso ≪≫
    (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := B)
      ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).obj M)).symm.toModuleIso

/-- 概要：多項式 pushout 比較の逆は b⊗m を C(b)⊗m へ送る。
方針：Mathlib の tensor 消去同型の純粋 tensor 公式。
規約：KST Lemma3.6。使われ方：比較の自然性と乗法整合性の検証。 -/
theorem polynomialPushoutModuleIso_inv_tmul (M : ModuleCat.{u} (MvPolynomial I A))
    (b : B) (m : (ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).obj M) :
    (polynomialPushoutModuleIso (B := B) M).inv.hom (b ⊗ₜ[A, algebraMap A B] m) =
      (MvPolynomial.C b) ⊗ₜ[MvPolynomial I A,
        algebraMap (MvPolynomial I A) (MvPolynomial I B)] m := by
  let := Module.restrictScalars A (MvPolynomial I A) M
  let : IsScalarTower A (MvPolynomial I A) M :=
    IsScalarTower.restrictScalars A (MvPolynomial I A) M
  change (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := MvPolynomial I B) M).symm
      ((Algebra.IsPushout.cancelBaseChange A B (MvPolynomial I A) (MvPolynomial I B) M).symm
        (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := B)
          ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).obj M)
          (b ⊗ₜ[A, algebraMap A B] m))) = _
  rw [_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView_tmul, Algebra.IsPushout.cancelBaseChange_symm_tmul]
  apply (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := MvPolynomial I B) M).injective
  rw [LinearEquiv.apply_symm_apply, _root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView_tmul]
  rfl

/-- 概要：多項式 pushout 比較の逆は加群射と可換。
方針：純粋 tensor の公式と係数拡大の加群射の計算を使う。
規約：KST Lemma3.6。使われ方：比較を複体へ持ち上げる。 -/
theorem polynomialPushoutModuleIso_inv_naturality
    {M N : ModuleCat.{u} (MvPolynomial I A)} (f : M ⟶ N) :
    (polynomialPushoutModuleIso (B := B) M).inv ≫
      (ModuleCat.restrictScalars (algebraMap B (MvPolynomial I B))).map
        ((ModuleCat.extendScalars (algebraMap (MvPolynomial I A) (MvPolynomial I B))).map f) =
    (ModuleCat.extendScalars (algebraMap A B)).map
        ((ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).map f) ≫
      (polynomialPushoutModuleIso (B := B) N).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    change ((ModuleCat.restrictScalars (algebraMap B (MvPolynomial I B))).map
        ((ModuleCat.extendScalars (algebraMap (MvPolynomial I A) (MvPolynomial I B))).map f)).hom
        ((polynomialPushoutModuleIso (B := B) M).inv.hom
          (b ⊗ₜ[A, algebraMap A B] m)) = _
    rw [polynomialPushoutModuleIso_inv_tmul]
    change ((ModuleCat.extendScalars (algebraMap (MvPolynomial I A) (MvPolynomial I B))).map f)
        ((MvPolynomial.C b) ⊗ₜ[MvPolynomial I A,
          algebraMap (MvPolynomial I A) (MvPolynomial I B)] m) =
      (polynomialPushoutModuleIso (B := B) N).inv.hom
        (b ⊗ₜ[A, algebraMap A B] f.hom m)
    rw [ModuleCat.ExtendScalars.map_tmul, polynomialPushoutModuleIso_inv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 概要：多項式 pushout の加群底変更比較は実際の自然同型。
方針：各対象での同型と逆写像の自然性から正方向の自然性を導く。
規約：KST Lemma3.6。使われ方：非有界複体への比較の持ち上げ。 -/
def polynomialPushoutModuleNatIso :
    ModuleCat.extendScalars (algebraMap (MvPolynomial I A) (MvPolynomial I B)) ⋙
        ModuleCat.restrictScalars (algebraMap B (MvPolynomial I B)) ≅
      ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A)) ⋙
        ModuleCat.extendScalars (algebraMap A B) :=
  NatIso.ofComponents (fun M => polynomialPushoutModuleIso M) (fun {M N} f => by
    apply (cancel_epi (polynomialPushoutModuleIso (B := B) M).inv).mp
    simp only [Functor.comp_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [polynomialPushoutModuleIso_inv_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id])

/-- 概要：多項式表示環の pushout に沿う底変更の二経路は非有界複体でも自然同型。
方針：加群の自然同型を mapHomologicalComplex で持ち上げる。
規約：KST Lemma3.6。使われ方：普遍基底上の導来底変更をチャート環上で計算する。 -/
def polynomialPushoutComplexNatIso :
    (ModuleCat.extendScalars
      (algebraMap (MvPolynomial I A) (MvPolynomial I B))).mapHomologicalComplex
        (.up ℤ) ⋙
      (ModuleCat.restrictScalars (algebraMap B (MvPolynomial I B))).mapHomologicalComplex (.up ℤ) ≅
    (ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).mapHomologicalComplex (.up ℤ) ⋙
      (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (polynomialPushoutModuleNatIso (A := A) (B := B) (I := I))
    (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A)) ⋙
          ModuleCat.extendScalars (algebraMap A B))) (.up ℤ)).symm

end SerrePositivity.KST.DerivedBlowup
