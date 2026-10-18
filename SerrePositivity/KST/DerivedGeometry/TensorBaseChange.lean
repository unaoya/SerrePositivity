module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# 非可換係数を保つテンソルの底変換

概要：可換環の塔に沿う二段の係数底変換を一段へまとめる。
方針：テンソル結合子と単位の同型を合成する。
規約：係数環 H の可換性・平坦性を要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン係数環層。
-/

@[expose] public section

noncomputable section

universe u v w t

open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

variable (A : Type u) (R : Type v) (S : Type w) (H : Type t)
  [CommRing A] [CommRing R] [CommRing S] [Ring H]
  [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S] [Algebra A H]

/--
概要：S ⊗_R (R ⊗_A H) を S ⊗_A H と S 代数として同定する。
方針：結合子の逆で左側を括り直し、S ⊗_R R の右単位を消す。
規約：H に R 作用や可換性を要求しない。
使われ方：KST D4、Toën §3.2 のアフィンの係数底変換。
-/
def tensorBaseChangeCancel : S ⊗[R] (R ⊗[A] H) ≃ₐ[S] S ⊗[A] H :=
  (Algebra.TensorProduct.assoc A R S S R H).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid R S S) (AlgEquiv.refl : H ≃ₐ[A] H))

/--
概要：二段の底変換の同型は s ⊗ (r ⊗ h) を (r • s) ⊗ h に送る。
方針：結合子、右単位、テンソル同型の純テンソルの計算式を使う。
規約：左因子のスカラー作用に R を明示する。
使われ方：KST D4、Toën §3.2 の制限写像との自然性。
-/
@[simp]
lemma tensorBaseChangeCancel_tmul (s : S) (r : R) (h : H) :
    tensorBaseChangeCancel A R S H (s ⊗ₜ[R] (r ⊗ₜ[A] h)) = (r • s) ⊗ₜ[A] h := rfl

/--
概要：底変換の逆同型は s ⊗ h を s ⊗ (1 ⊗ h) に送る。
方針：右単位と結合子の逆の計算式を使う。
規約：H に R 上の代数構造を導入しない。
使われ方：KST D4、Toën §3.2 の前層比較の逆射。
-/
@[simp]
lemma tensorBaseChangeCancel_symm_tmul (s : S) (h : H) :
    (tensorBaseChangeCancel A R S H).symm (s ⊗ₜ[A] h) =
      s ⊗ₜ[R] (1 ⊗ₜ[A] h) := rfl

/--
概要：右因子からの R 作用で (H ⊗_A R) ⊗_R S を H ⊗_A S と環同型にする。
方針：因子の交換、左側の底変換の消去、再び因子の交換を合成する。
規約：H ⊗_A R の R 作用は右因子から与え、H 自身には R 作用を要求しない。
使われ方：KST D4、Toën §3.2 の係数テンソル前層の底変換。
-/
def tensorBaseChangeRight :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (H ⊗[A] R) ⊗[R] S ≃+* H ⊗[A] S := by
  letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.congr (Algebra.TensorProduct.commRight A R H).symm
      (AlgEquiv.refl : S ≃ₐ[R] S)).toRingEquiv.trans
    ((Algebra.TensorProduct.comm R (R ⊗[A] H) S).toRingEquiv.trans
      ((tensorBaseChangeCancel A R S H).toRingEquiv.trans
        (Algebra.TensorProduct.comm A S H).toRingEquiv))

/--
概要：右側の係数底変換の同型は (h ⊗ r) ⊗ s を h ⊗ (r • s) に送る。
方針：因子の交換と底変換の消去を純テンソル上で計算する。
規約：右因子由来の R 作用を明示する。
使われ方：KST D4、Toën §3.2 の前層の制限との両立。
-/
@[simp]
lemma tensorBaseChangeRight_tmul (h : H) (r : R) (s : S) :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    tensorBaseChangeRight A R S H ((h ⊗ₜ[A] r) ⊗ₜ[R] s) =
      h ⊗ₜ[A] (r • s) := rfl

/--
概要：右側の係数底変換の逆同型は h ⊗ s を (h ⊗ 1) ⊗ s に送る。
方針：合成した各環同型の逆を純テンソル上で計算する。
規約：R の単位元を中間因子に置く。
使われ方：KST D4、Toën §3.2 の前層の比較の逆射。
-/
@[simp]
lemma tensorBaseChangeRight_symm_tmul (h : H) (s : S) :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (tensorBaseChangeRight A R S H).symm (h ⊗ₜ[A] s) =
      (h ⊗ₜ[A] (1 : R)) ⊗ₜ[R] s := rfl

/--
概要：係数底変換の環同型は構造環 S の右因子への包含を保つ。
方針：二重の純テンソルの計算式で中間の元を 1 とする。
規約：H 側の単位元を保つ標準的な比較を使う。
使われ方：KST D4、Toën §3.2 の構造層射との両立。
-/
@[simp]
lemma tensorBaseChangeRight_unit (s : S) :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    tensorBaseChangeRight A R S H ((1 : H ⊗[A] R) ⊗ₜ[R] s) =
      (1 : H) ⊗ₜ[A] s := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.TensorProduct.one_def, tensorBaseChangeRight_tmul, one_smul]

/--
概要：右側の係数底変換は S から別の R 代数への写像に自然。
方針：二重の純テンソルへ帰着し、R 代数準同型の線形性を使う。
規約：二つの A 作用は R を経由する塔の条件で指定する。
使われ方：KST D4、Toën §3.2 のテンソル前層の制限との自然性。
-/
lemma tensorBaseChangeRight_naturality
    {T : Type*} [CommRing T] [Algebra R T] [Algebra A T] [IsScalarTower A R T]
    (f : S →ₐ[R] T) :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    ∀ x : (H ⊗[A] R) ⊗[R] S,
      tensorBaseChangeRight A R T H
          (Algebra.TensorProduct.map (AlgHom.id R (H ⊗[A] R)) f x) =
        Algebra.TensorProduct.map (AlgHom.id A H) (f.restrictScalars A)
          (tensorBaseChangeRight A R S H x) := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul y s =>
    induction y using TensorProduct.inductionOn with
    | tmul h r =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        tensorBaseChangeRight_tmul, AlgHom.restrictScalars_apply, map_smul]
    | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

end SerrePositivity.KST.DerivedGeometry
