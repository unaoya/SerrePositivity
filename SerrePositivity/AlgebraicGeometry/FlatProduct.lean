module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
概要：KST §5、Stacks 05FS の局所化と完備化の有限積の平坦性。
方針：イデアルとのテンソル単射判定を、積に分配する同型の各成分で確認する。
規約：任意の二つの平坦加群の有限積を扱う。
使われ方：局所化と完備化の忠実平坦被覆。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：二つの平坦加群の積は平坦。
方針：右の積に関するテンソル分配同型とイデアルの単射判定を使う。
規約：KST §5、Stacks 05FS、基礎環の Noether 性は不要。
使われ方：局所化環と完備化環の積の平坦性。
-/
theorem flat_product
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module.Flat R N] : Module.Flat R (M × N) := by
  apply (Module.Flat.iff_rTensor_injective' (R := R) (M := M × N)).mpr
  intro I x y hxy
  let EI := TensorProduct.prodRight R R I M N
  let ER := TensorProduct.prodRight R R R M N
  have hcomm : ER.toLinearMap.comp (I.subtype.rTensor (M × N)) =
      (LinearMap.prodMap (I.subtype.rTensor M) (I.subtype.rTensor N)).comp EI.toLinearMap := by
    apply TensorProduct.ext'
    intro r v
    rfl
  have h := congrArg ER hxy
  change (ER.toLinearMap.comp (I.subtype.rTensor (M × N))) x =
    (ER.toLinearMap.comp (I.subtype.rTensor (M × N))) y at h
  rw [hcomm] at h
  apply EI.injective
  apply Prod.ext
  · exact (Module.Flat.rTensor_preserves_injective_linearMap I.subtype
      (Submodule.injective_subtype I)) (congrArg Prod.fst h)
  · exact (Module.Flat.rTensor_preserves_injective_linearMap I.subtype
      (Submodule.injective_subtype I)) (congrArg Prod.snd h)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
