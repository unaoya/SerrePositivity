module

public import SerrePositivity.AlgebraicGeometry.IdealTensorMap
public import SerrePositivity.AlgebraicGeometry.PureTransformImage

/-!
概要：KST §5、Stacks 0815 のイデアル加群の純変換を拡大イデアルに同定する。
方針：乗法写像の核の消滅と標的の正則作用を組み合わせる。
規約：境界元の一つの冪がイデアルに入ると仮定する。
使われ方：blowup チャート上のイデアル加群の平坦化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (f : R) (n : ℕ) (hn : f ^ n ∈ I)

include hn

/--
概要：境界の冪が入るイデアルの乗法写像の核はその冪で消える。
方針：イデアルの各元による核の消滅を指定された冪に適用する。
規約：KST §5、Stacks 0815、基底変更の平坦性を仮定しない。
使われ方：純変換の核の同定。
-/
theorem idealTensorMap_ker_boundary_annihilated (z : S ⊗[R] I)
    (hz : idealTensorMap I z = 0) : (algebraMap R S f) ^ n • z = 0 := by
  rw [← map_pow]
  exact idealTensorMap_ker_annihilated I ⟨f ^ n, hn⟩ z hz

/--
概要：イデアル加群の基底変更の純変換と拡大イデアルの線形同型。
方針：乗法写像の核を境界ねじれと同定し、その像の計算を使う。
規約：KST §5、Stacks 0815、境界元の像は係数環で正則とする。
使われ方：例外イデアルの自由化から純変換の平坦性を導く。
-/
def idealPureTransformEquiv (hf : IsRegular (algebraMap R S f)) :
    modulePureTransform (algebraMap R S f) (S ⊗[R] I) ≃ₗ[S]
      I.map (algebraMap R S) :=
  (modulePureTransformEquivImage (algebraMap R S f) (idealTensorMap I)
    (Module.Flat.isSMulRegular_of_isRegular hf)
    (fun z hz => ⟨n, idealTensorMap_ker_boundary_annihilated I f n hn z hz⟩)).trans
      (LinearEquiv.ofEq _ _ (idealTensorMap_range I))

/--
概要：イデアルの純変換の比較同型は乗法写像を保存する。
方針：核による商と像の同型の代表元上の公式を使う。
規約：KST §5、Stacks 0815、拡大イデアルから係数環への包含で比較する。
使われ方：チャート上の純変換の自明化の交換式。
-/
theorem idealPureTransformEquiv_mk (hf : IsRegular (algebraMap R S f))
    (z : S ⊗[R] I) :
    (idealPureTransformEquiv I f n hn hf (Submodule.Quotient.mk z) : S) =
      idealTensorMap I z := rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
