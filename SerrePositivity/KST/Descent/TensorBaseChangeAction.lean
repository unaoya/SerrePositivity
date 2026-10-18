module

public import SerrePositivity.KST.Descent.GeometricFiberTransitivity

/-!
# 係数拡大後の環の作用

## 概要
T の A 線形な群作用を、B ⊗_A T の B 線形な作用へ拡大する。

## 方針
B 側を恒等射、T 側を指定群元の代数射とするテンソル積の写像を使う。

## 規約
B を左因子とし、標準の B 代数構造を使う。B への群作用は要求しない。

## 使われ方
論文 定理 3.1 の基底変更後の幾何的推移性と、閉中心上の帰納。
-/

@[expose] public section

universe u

open TensorProduct

namespace SerrePositivity.KST.Descent

variable {A B T G : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：基底変更後の群元の指定代数射（論文 定理 3.1）。
方針：左因子を固定して右因子へ元の作用を適用する。
規約：A 代数射として指定する。
使われ方：基底変更した環の群作用の構成。 -/
noncomputable def tensorBaseChangeHom (g : G) : B ⊗[A] T →ₐ[A] B ⊗[A] T :=
  Algebra.TensorProduct.map (AlgHom.id A B) (MulSemiringAction.toAlgHom A T g)

/-- 概要：指定代数射の単位の法則（論文 §3）。
方針：純テンソル上の等式で検査する。
規約：環の自己準同型の等式。
使われ方：作用の単位の法則。 -/
theorem tensorBaseChangeHom_one : tensorBaseChangeHom (A := A) (B := B) (T := T) (1 : G) =
    AlgHom.id A (B ⊗[A] T) := by
  apply AlgHom.toLinearMap_injective
  ext b t
  simp [tensorBaseChangeHom]

/-- 概要：指定代数射は群の積を合成へ送る（論文 §3）。
方針：純テンソル上で元の群作用の積の法則を使う。
規約：右因子の作用の向きを保持する。
使われ方：基底変更後の群作用の構成。 -/
theorem tensorBaseChangeHom_mul (g h : G) :
    tensorBaseChangeHom (A := A) (B := B) (T := T) (g * h) =
      (tensorBaseChangeHom g).comp (tensorBaseChangeHom h) := by
  apply AlgHom.toLinearMap_injective
  ext b t
  simp [tensorBaseChangeHom, mul_smul]

/-- 概要：係数拡大後の環の群作用（論文 定理 3.1）。
方針：指定代数射の群の法則と加法・乗法の保存を使う。
規約：左因子 B を固定し、右因子 T のみを動かす。
使われ方：既存の幾何的推移性の定義を係数拡大後にも適用する。 -/
noncomputable instance tensorBaseChangeMulSemiringAction : MulSemiringAction G (B ⊗[A] T) where
  smul g z := tensorBaseChangeHom g z
  one_smul z := by
    change tensorBaseChangeHom (1 : G) z = z
    rw [tensorBaseChangeHom_one]
    rfl
  mul_smul g h z := by
    change tensorBaseChangeHom (g * h) z = tensorBaseChangeHom g (tensorBaseChangeHom h z)
    rw [tensorBaseChangeHom_mul]
    rfl
  smul_zero g := map_zero (tensorBaseChangeHom g)
  smul_add g x y := map_add (tensorBaseChangeHom g) x y
  smul_one g := map_one (tensorBaseChangeHom g)
  smul_mul g x y := map_mul (tensorBaseChangeHom g) x y

/-- 概要：係数拡大後の作用は B 線形（論文 定理 3.1）。
方針：左因子のスカラーは固定され、作用は乗法を保存する。
規約：標準の B 代数構造に関する線形性。
使われ方：Spec B 上の作用と B に関する幾何的推移性。 -/
instance tensorBaseChange_smulCommClass : SMulCommClass G B (B ⊗[A] T) where
  smul_comm g b z := by
    change tensorBaseChangeHom g (b • z) = b • tensorBaseChangeHom g z
    simp [Algebra.smul_def, tensorBaseChangeHom, Algebra.TensorProduct.algebraMap_apply]

/-- 概要：純テンソル上の係数拡大作用の公式（論文 §3）。
方針：テンソル積の map の定義を使う。
規約：左因子は固定される。
使われ方：幾何ファイバーの同型と作用の両立。 -/
@[simp] theorem tensorBaseChange_smul_tmul (g : G) (b : B) (t : T) :
    g • (b ⊗ₜ[A] t) = b ⊗ₜ[A] (g • t) := rfl

end SerrePositivity.KST.Descent
