module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：KST §5、Stacks 0810 の特別な局所化で必要な基礎環上の平坦性の保存。
方針：混合テンソル積の結合同型を介して二つの平坦性を順に使う。
規約：加群の基礎環とテンソル積を取る代数を明示する。
使われ方：代数の素点で局所化した加群の基礎環上の平坦性を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
open TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/--
概要：代数上平坦な加群とのテンソル積は基礎環上の平坦性を保つ。
方針：混合結合同型により包含のテンソル化を二段階に分解する。
規約：KST §5、Stacks 0810、代数自身の基礎環上の平坦性は不要。
使われ方：代数上の局所化による基礎環上の平坦性の保存。
-/
theorem relativeFlat_tensor [Module.Flat R M] [Module.Flat S N] :
    Module.Flat R (N ⊗[S] M) := by
  apply Module.Flat.iff_lTensor_injectiveₛ.mpr
  intro P _ _ I
  let g : (M ⊗[R] I) →ₗ[S] (M ⊗[R] P) :=
    AlgebraTensorModule.lTensor S M I.subtype
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective
  have hNg : Function.Injective (g.lTensor N) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  let eI := AlgebraTensorModule.assoc R S S N M I
  let eP := AlgebraTensorModule.assoc R S S N M P
  have hsquare :
      (eP.toLinearMap.restrictScalars R).comp (I.subtype.lTensor (N ⊗[S] M)) =
        ((g.lTensor N).restrictScalars R).comp (eI.toLinearMap.restrictScalars R) := by
    ext z i
    induction z using TensorProduct.inductionOn with
    | tmul n m => rfl
    | add x y hx hy =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy
  intro x y hxy
  apply eI.injective
  apply hNg
  have h := congrArg eP hxy
  change ((eP.toLinearMap.restrictScalars R).comp
      (I.subtype.lTensor (N ⊗[S] M))) x =
    ((eP.toLinearMap.restrictScalars R).comp
      (I.subtype.lTensor (N ⊗[S] M))) y at h
  rw [hsquare] at h
  exact h

variable {C : Type*} [CommRing C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/--
概要：代数の局所化後も加群の基礎環上の平坦性は保たれる。
方針：局所化環の代数上の平坦性を混合テンソル積の平坦性に適用する。
規約：KST §5、Stacks 0810、局所化する乗法的集合は代数内に取る。
使われ方：ファイバーの一般点に対応する拡大素点での局所自由性の準備。
-/
theorem relativeFlat_localization [Module.Flat R M] (T : Submonoid S)
    [IsLocalization T C] : Module.Flat R (C ⊗[S] M) := by
  let : Module.Flat S C := IsLocalization.flat C T
  exact relativeFlat_tensor (R := R) (S := S) (M := M) (N := C)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
