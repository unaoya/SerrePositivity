module

public import SerrePositivity.AlgebraicGeometry.PureTransformUniversalExact
public import Mathlib.RingTheory.Flat.Equalizer

/-!
概要：普遍単射な短完全列の純変換で、両端の平坦性から中央の平坦性を得る。
方針：純変換の完全性を使い、任意の単射とのテンソル積について図式を追う。
規約：一つの境界元を持つアフィンチャート上で述べる。
使われ方：余核の台の次元を下げた後、元の加群の平坦性を得る。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open Function
open scoped TensorProduct

private theorem flat_middle_of_shortExact
    {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Injective f) (hg : Surjective g) (hex : Exact f g) :
    Module.Flat R N := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro X Y _ _ _ _ j hj
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hzP : g.lTensor X z = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := P) j hj
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hz, map_zero, map_zero]
  obtain ⟨w, hw⟩ := (lTensor_exact X hex hg z).mp hzP
  have hwY : j.rTensor M w = 0 := by
    apply g.lTensor_injective_of_exact_of_flat hg f hf hex Y
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hw, hz, map_zero]
  have hw0 : w = 0 :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := M) j hj
      (by rw [hwY, map_zero])
  rw [← hw, hw0, map_zero]

/--
概要：普遍単射を左端とする短完全列で、底変換後の左端と余核の純変換が平坦なら中央も平坦。
方針：底変換後の純変換の短完全性を使い、平坦加群の拡大として中央を扱う。
規約：境界元は底変換先の環の元とする。
使われ方：Stacks 0815 で、台の次元を下げた余核の平坦化から元の平坦化に戻す。
-/
theorem modulePureTransform_baseChange_flat_of_flat_ends
    {R A M N P : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (a : A) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Exact f g) (hg : Surjective g)
    (hf : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q], Injective (f.lTensor Q))
    [Module.Flat A (modulePureTransform a (A ⊗[R] M))]
    [Module.Flat A (modulePureTransform a (A ⊗[R] P))] :
    Module.Flat A (modulePureTransform a (A ⊗[R] N)) := by
  obtain ⟨hf', hex', hg'⟩ :=
    pureTransform_baseChange_shortExact_of_universal_injective a f g hex hg hf
  exact flat_middle_of_shortExact _ _ hf' hg' hex'

end SerrePositivity.AlgebraicGeometry
