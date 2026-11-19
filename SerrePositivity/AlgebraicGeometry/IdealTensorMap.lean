module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：KST §5、Stacks 0815 のイデアル加群の純変換に使う乗法写像。
方針：イデアルの包含を基底変更して、係数環とのテンソル積の同型を合成する。
規約：環準同型は代数構造で指定する。
使われ方：blowup チャート上で基底変更加群と拡大イデアルを比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/--
概要：イデアル加群の基底変更から係数環への乗法写像。
方針：包含の基底変更とテンソル積の右単位同型を合成する。
規約：KST §5、Stacks 0815、平坦な基底変更を仮定しない。
使われ方：純変換を拡大イデアルと同定する写像。
-/
def idealTensorMap : S ⊗[R] I →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ I.subtype.baseChange S

/--
概要：イデアルの乗法写像の純テンソル上の値。
方針：基底変更と右単位同型の定義を使う。
規約：KST §5、Stacks 0815、係数とイデアル元の順序を固定する。
使われ方：核と像の計算。
-/
@[simp] theorem idealTensorMap_tmul (s : S) (a : I) :
    idealTensorMap (S := S) I (s ⊗ₜ a) = s * algebraMap R S a.1 := by
  simp [idealTensorMap, Algebra.smul_def, mul_comm]

/--
概要：イデアルの乗法写像の像は拡大イデアル。
方針：純テンソルの像による包含と、元の生成元の持ち上げを使う。
規約：KST §5、Stacks 0815、一般の基底変更を扱う。
使われ方：商による純変換から拡大イデアルへの同型。
-/
theorem idealTensorMap_range :
    LinearMap.range (idealTensorMap (S := S) I) = I.map (algebraMap R S) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul s a =>
      rw [idealTensorMap_tmul]
      exact Ideal.mul_mem_left _ s (Ideal.mem_map_of_mem _ a.2)
    | add x y hx hy => simpa using (I.map (algebraMap R S)).add_mem hx hy
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact ⟨1 ⊗ₜ ⟨a, ha⟩, by simp⟩

/--
概要：イデアル元の係数作用と乗法写像による作用の関係式。
方針：純テンソル上でイデアルの二元の積を交換し、加法で広げる。
規約：KST §5、Stacks 0815、a は元のイデアルの元。
使われ方：乗法写像の核がイデアルの元で消えること。
-/
theorem idealTensorMap_smul (a : I) (z : S ⊗[R] I) :
    algebraMap R S a.1 • z =
      idealTensorMap I z • ((1 : S) ⊗ₜ[R] a) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, add_smul, hx, hy]
  | tmul s b =>
    rw [idealTensorMap_tmul]
    calc
      algebraMap R S a.1 • (s ⊗ₜ[R] b) = (a.1 • s) ⊗ₜ[R] b := by
        simp [TensorProduct.smul_tmul', Algebra.smul_def]
      _ = s ⊗ₜ[R] (a.1 • b) := TensorProduct.smul_tmul _ _ _
      _ = s ⊗ₜ[R] (b.1 • a) := by
        congr 1
        exact Subtype.ext (mul_comm _ _)
      _ = (b.1 • s) ⊗ₜ[R] a := (TensorProduct.smul_tmul _ _ _).symm
      _ = (s * algebraMap R S b.1) • ((1 : S) ⊗ₜ[R] a) := by
        simp [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]

/--
概要：乗法写像の核は元のイデアルの各元の像で消える。
方針：テンソル上の作用の関係式に核の等式を代入する。
規約：KST §5、Stacks 0815、像中心の単項性はまだ不要。
使われ方：チャート上で核が境界ねじれに含まれること。
-/
theorem idealTensorMap_ker_annihilated (a : I) (z : S ⊗[R] I)
    (hz : idealTensorMap I z = 0) : algebraMap R S a.1 • z = 0 := by
  rw [idealTensorMap_smul, hz, zero_smul]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
