module

public import SerrePositivity.AlgebraicGeometry.ScalarProductTensorComparison
public import SerrePositivity.AlgebraicGeometry.ModuleMittagLeffler
public import Mathlib.RingTheory.Flat.Tensor

/-!
概要：KST §5、Stacks 05DJ・05D0, Lemma 10.91.3 の Noether 環の任意の積の平坦 Mittag–Leffler 性。
方針：任意の加群に対する係数積比較の単射性から、イデアルの判定と二つの積の成分比較を使う。
規約：積の添字に有限性を課さず、基礎環は Noether とする。
使われ方：自由加群の完備化の Mittag–Leffler 性への原典経路。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：係数環の積を左因子とするテンソルの成分比較線形写像。
方針：左右交換同型と既存の右因子の係数積比較を合成する。
規約：KST §5、Stacks 05D0、各成分は係数関数の値による作用。
使われ方：係数環の積自体の Mittag–Leffler 性を判定する。
-/
def piScalarLeftHom (R A Q : Type*) [CommRing R] [AddCommGroup Q] [Module R Q] :
    (A → R) ⊗[R] Q →ₗ[R] (A → Q) :=
  (TensorProduct.piScalarRightHom R R Q A).comp (TensorProduct.comm R (A → R) Q).toLinearMap

/--
概要：左因子の係数積比較の純テンソル上の成分公式。
方針：左右交換と右因子の係数積比較の公式を使う。
規約：KST §5、Stacks 05D0、有限性は不要。
使われ方：二つの積の比較写像の各成分を照合する。
-/
theorem piScalarLeftHom_tmul
    {R A Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q] (v : A → R) (q : Q) :
    piScalarLeftHom R A Q (v ⊗ₜ[R] q) = fun a => v a • q := by
  simp [piScalarLeftHom]

/--
概要：Noether 基底で左因子の係数積比較は任意の加群に対し単射。
方針：右因子での単射性と左右交換同型を合成する。
規約：KST §5、Stacks 05D0、試験加群の平坦性は不要。
使われ方：任意の加群族の積比較の単射性を示す。
-/
theorem piScalarLeftHom_injective_of_noetherian
    (R A Q : Type*) [CommRing R] [IsNoetherianRing R] [AddCommGroup Q] [Module R Q] :
    Function.Injective (piScalarLeftHom R A Q) :=
  (piScalarRightHom_injective_of_noetherian R Q A).comp (TensorProduct.comm R (A → R) Q).injective

/--
概要：Noether 環の任意のコピーの積は基礎環上平坦。
方針：イデアルのテンソル単射性を、係数積比較と各成分でのイデアル包含の単射性から得る。
規約：KST §5、Stacks 05D0, Lemma 10.91.3、積の添字は任意。
使われ方：自由加群の完備化の原典で必要な積の平坦性。
-/
theorem flat_pi_of_noetherian
    (R A : Type*) [CommRing R] [IsNoetherianRing R] : Module.Flat R (A → R) := by
  apply (Module.Flat.iff_rTensor_injective' (R := R) (M := A → R)).mpr
  intro I x y hxy
  apply piScalarRightHom_injective_of_noetherian R I A
  funext a
  apply Subtype.val_injective
  have h := congrArg (fun z : R ⊗[R] (A → R) => TensorProduct.piScalarRightHom R R R A z a) hxy
  simpa only [piScalarRightHom_rTensor_apply, Submodule.subtype_apply] using h

/--
概要：係数積比較と試験加群族の積比較は二つの成分の順序を交換しても同じ値を返す。
方針：純テンソルで作用の成分を照合し、加法で延長する。
規約：KST §5、Stacks 05D0、二つの添字族はいずれも任意。
使われ方：係数環の積の Mittag–Leffler 性。
-/
theorem piScalarLeftHom_piRightHom_apply
    {R A J : Type*} [CommRing R] (P : J → Type*)
    [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
    (x : (A → R) ⊗[R] (∀ j, P j)) (a : A) (j : J) :
    piScalarLeftHom R A (∀ j, P j) x a j =
      piScalarLeftHom R A (P j) (TensorProduct.piRightHom R R (A → R) P x j) a := by
  induction x using TensorProduct.inductionOn with
  | tmul v p => simp only [piScalarLeftHom_tmul, TensorProduct.piRightHom_tmul, Pi.smul_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/--
概要：Noether 環の任意のコピーの積は Mittag–Leffler 加群。
方針：各係数成分で試験族の積比較を照合し、係数積比較の単射性で元のテンソルを区別する。
規約：KST §5、Stacks 05D0, Lemma 10.91.3、環と積の添字は同じ宇宙に置く。
使われ方：完備化から係数環の積への普遍単射性と組み合わせる。
-/
theorem isModuleMittagLeffler_pi_of_noetherian
    (R A : Type u) [CommRing R] [IsNoetherianRing R] : IsModuleMittagLeffler R (A → R) := by
  intro J P hP hRP x y hxy
  apply piScalarLeftHom_injective_of_noetherian R A (∀ j, P j)
  funext a j
  rw [piScalarLeftHom_piRightHom_apply, piScalarLeftHom_piRightHom_apply, hxy]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
