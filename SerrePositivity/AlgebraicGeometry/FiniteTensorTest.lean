module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
概要：KST §5、Stacks 05BC・05DJ の普遍単射性の有限生成試験。
方針：テンソルの一元を有限生成部分から持ち上げ、終域の平坦性で零を戻す。
規約：基礎環の Noether 性を要求しない。
使われ方：自由完備化の積埋め込みの有限テンソルの単射性を任意のテンソルへ広げる。
-/

@[expose] public section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：平坦な終域への線形写像のテンソル単射性は、有限生成な試験加群だけで判定できる。
方針：核の元を有限部分から持ち上げ、終域の平坦性と有限試験の単射性を順に使う。
規約：KST §5、Stacks 05BC・05DJ、始域の平坦性は仮定しない。
使われ方：自由加群の完備化から積への埋め込みの普遍単射性。
-/
theorem lTensor_injective_of_finite_tests
    {R L P : Type u} [CommRing R] [AddCommGroup L] [Module R L]
    [AddCommGroup P] [Module R P] [Module.Flat R P] (e : L →ₗ[R] P)
    (he : ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      Function.Injective (e.lTensor N))
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (e.lTensor N) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨N', hfin, hcapture⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {x} (Set.finite_singleton x)
  let := hfin
  obtain ⟨y, hy⟩ := hcapture (Set.mem_singleton x)
  have hcomm : (e.lTensor N).comp (N'.subtype.rTensor L) =
      (N'.subtype.rTensor P).comp (e.lTensor N') := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hz : N'.subtype.rTensor P (e.lTensor N' y) = 0 := by
    change ((N'.subtype.rTensor P).comp (e.lTensor N')) y = 0
    rw [← hcomm]
    change e.lTensor N (N'.subtype.rTensor L y) = 0
    rw [hy]
    exact hx
  have hz' : e.lTensor N' y = 0 :=
    (Module.Flat.rTensor_preserves_injective_linearMap N'.subtype
      (Submodule.injective_subtype N')) (by simpa using hz)
  have hy0 : y = 0 := (he N') (by simpa using hz')
  rw [← hy, hy0, map_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
