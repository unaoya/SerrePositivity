module

public import SerrePositivity.BhattScholze.Andre.SemilinearTensorBaseChange
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# André E1・E2：係数環全体の自己同型に沿う実引戻し

## 概要

係数環 A の自己同型に関して半線形な環同型は、A 全体で取る通常テンソル引戻しの
代数同型を与える。BS Rem 7.15(1)（著者版 p.62）の φ_A 引戻しを記述する。

## 方針

左の A を TensorBaseCopy A で区別し、既存の半線形テンソル同型を適用する。
原典とは異なる、実テンソルの普遍性を使う形式化上の経路。

## 規約

型の写しは宇宙を上げずに二つの係数作用を区別するために使う。
自己同型・二つの係数射・半線形性を全て明示し、商や正則性は仮定しない。

## 使われ方

実 Hodge–Tate ϖ 商の係数比較を、商環間だけでなく A 全体の Frobenius 引戻しに適用する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct

/-- 概要：左係数環と元の係数環の作用を区別する同じ宇宙の型の写し。
方針：一つの値を持つ構造体として与える。
規約：元の環の情報を追加も削除もしない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の自己同型による引戻し。 -/
structure TensorBaseCopy (A : Type u) where
  value : A

/-- 概要：左係数環の写しは元の係数環と全単射。
方針：値を取り出す写像と一つの値を包む写像を逆とする。
規約：宇宙を変えない全単射。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実引戻しの環構造を定める。 -/
def tensorBaseCopyEquiv (A : Type u) : TensorBaseCopy A ≃ A where
  toFun := TensorBaseCopy.value
  invFun := TensorBaseCopy.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- 概要：係数環の写しには元の可換環構造を移す。
方針：値を取り出す全単射で環演算を移送する。
規約：自己同型によるスカラー作用はこの環構造と区別して後で指定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の通常テンソル。 -/
instance tensorBaseCopyCommRing {A : Type u} [CommRing A] : CommRing (TensorBaseCopy A) :=
  (tensorBaseCopyEquiv A).commRing

/-- 概要：係数環の写しと元の環は値を取り出す環同型で結ばれる。
方針：環構造を移した全単射を環同型へ強める。
規約：順方向は写しから元の A への射。
使われ方：BS Rem 7.15(1)（著者版 p.62）の左右の係数作用を明示する。 -/
def tensorBaseCopyRingEquiv (A : Type u) [CommRing A] : TensorBaseCopy A ≃+* A :=
  { tensorBaseCopyEquiv A with map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- 概要：自己同型に関して半線形な環同型は係数環全体の実引戻しを計算する。
方針：左係数環の写しとの同型を使い、通常テンソルの半線形比較を適用する。
規約：源と標的の自然な係数射を引数として固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の A 上の φ_A 引戻し。 -/
def automorphismTensorPullbackAlgEquiv (α : A ≃+* A) (q : A →+* B) (r : A →+* C)
    (F : B ≃+* C) (hF : ∀ a : A, F (q a) = r (α a)) :
    let := q.toAlgebra
    let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
    let := (α.trans (tensorBaseCopyRingEquiv A).symm).toRingHom.toAlgebra
    TensorBaseCopy A ⊗[A] B ≃ₐ[TensorBaseCopy A] C := by
  let := q.toAlgebra
  let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
  exact tensorBaseChangeAlgEquivOfSemilinearRingEquiv
    (α.trans (tensorBaseCopyRingEquiv A).symm) F (by
      intro a
      change F (q a) = r ((tensorBaseCopyRingEquiv A)
        ((tensorBaseCopyRingEquiv A).symm (α a)))
      rw [RingEquiv.apply_symm_apply]
      exact hF a)

/-- 概要：係数環全体の引戻し比較は単純テンソルを係数像と半線形像の積へ送る。
方針：既存の単純テンソル公式を係数環の写しへ特殊化する。
規約：左係数は写しの元を元の A に戻して評価する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の標準係数と根変数の追跡。 -/
theorem automorphismTensorPullbackAlgEquiv_tmul (α : A ≃+* A) (q : A →+* B)
    (r : A →+* C) (F : B ≃+* C) (hF : ∀ a : A, F (q a) = r (α a))
    (a : A) (b : B) :
    let := q.toAlgebra
    let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
    let := (α.trans (tensorBaseCopyRingEquiv A).symm).toRingHom.toAlgebra
    automorphismTensorPullbackAlgEquiv α q r F hF
      ((⟨a⟩ : TensorBaseCopy A) ⊗ₜ[A] b) = r a * F b := by
  let := q.toAlgebra
  let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
  rfl

end SerrePositivity.BhattScholze.Andre
