module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：KST Lemma3.6 の底変更比較で使う、束ねた係数拡大と通常の tensor の表示比較。
方針：係数因子の二つのスカラー作用を係数構造射の積公式で比較する。
規約：既存 ModuleCat の定義を変更しない。
使われ方：多項式 pushout の tensor 消去同型を実際の係数拡大関手へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.CommutativeAlgebra.Module

open _root_.CategoryTheory
open scoped _root_.TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- 概要：係数制限した B と代数の A 加群 B の恒等線形同型。
方針：二つのスカラー作用を Algebra.smul_def で同定する。
規約：KST Lemma3.6。使われ方：tensor の係数因子の型比較。 -/
def scalarCoefficientView :
    ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[A] B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a b := by
    change (fun x y : B => x * y) (algebraMap A B a) b =
      (fun (x : A) (y : B) => x • y) a b
    exact (Algebra.smul_def (A := B) a b).symm

/-- 概要：束ねた係数拡大と通常の代数 tensor の標準線形同型。
方針：係数因子の恒等同型を tensor し、純粋 tensor で B 線形性を確認する。
規約：KST Lemma3.6。使われ方：pushout 比較の source と target の正規化。 -/
def scalarExtensionTensorView (M : ModuleCat.{u} A) :
    ((ModuleCat.extendScalars (algebraMap A B)).obj M) ≃ₗ[B] B ⊗[A] M := by
  let e := TensorProduct.congr (_root_.SerrePositivity.CommutativeAlgebra.Module.scalarCoefficientView (A := A) (B := B)) (LinearEquiv.refl A M)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro b z
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
    change e ((show (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
      from (fun x y : B => x * y) b c) ⊗ₜ[A] m) = b • e (c ⊗ₜ[A] m)
    simp only [e, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rfl
  | add x y hx hy =>
    change e (b • (x + y)) = b • e (x + y)
    change e (b • x) = b • e x at hx
    change e (b • y) = b • e y at hy
    rw [smul_add, e.map_add, e.map_add, hx, hy, smul_add]

/-- 概要：係数拡大表示の同型は純粋 tensor を保つ。
方針：係数因子の恒等写像と tensor 同型の公式。
規約：KST Lemma3.6。使われ方：底変更比較の自然性。 -/
theorem scalarExtensionTensorView_tmul (M : ModuleCat.{u} A) (b : B) (m : M) :
    _root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView (B := B) M
      ((TensorProduct.tmul A b m : (ModuleCat.extendScalars (algebraMap A B)).obj M)) =
        b ⊗ₜ[A] m := by
  change TensorProduct.congr _root_.SerrePositivity.CommutativeAlgebra.Module.scalarCoefficientView (LinearEquiv.refl A M) _ = _
  rw [TensorProduct.congr_tmul]
  rfl

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra B C]
  [SMulCommClass B A C]

/-- 概要：係数制限した tensor の作用と通常の代数 tensor の作用の恒等比較。
方針：純粋 tensor 上で Algebra.smul_def を使い、加法で延長する。
規約：KST Lemma3.6。使われ方：pushout の通常の tensor 消去同型との接続。 -/
def scalarRestrictionTensorView (M : ModuleCat.{u} B) :
    ((ModuleCat.restrictScalars (algebraMap A C)).obj (ModuleCat.of C (C ⊗[B] M))) ≃ₗ[A]
      C ⊗[B] M where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
      change ((algebraMap A C a * c) ⊗ₜ[B] m) = (a • c) ⊗ₜ[B] m
      rw [Algebra.smul_def]
    | add x y hx hy =>
      change _ = _ at hx hy ⊢
      simp only [smul_add, hx, hy]

end SerrePositivity.CommutativeAlgebra.Module
