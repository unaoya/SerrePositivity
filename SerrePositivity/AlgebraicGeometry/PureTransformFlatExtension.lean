module

public import SerrePositivity.AlgebraicGeometry.LocalUniversalInjectivity
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


/--
概要：普遍単射の標的が係数拡大後に平坦なら、余核も係数拡大後に平坦。
方針：普遍単射性と右完全性を係数拡大に移し、拡大後の余核と比較する。
規約：余核は値域による商とする。
使われ方：Stacks 0815 で、境界外の余核の平坦性を帰納の仮定に渡す。
-/
theorem flat_cokernel_baseChange_of_lTensor_injective
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat A (A ⊗[R] N)] (f : M →ₗ[R] N)
    (hf : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q], Injective (f.lTensor Q)) :
    Module.Flat A (A ⊗[R] (N ⧸ LinearMap.range f)) := by
  let q := (LinearMap.range f).mkQ
  have hsurj : Surjective (q.baseChange A) :=
    LinearMap.baseChange_surjective A (Submodule.mkQ_surjective _)
  have hex := lTensor_exact A f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker (q.baseChange A) = LinearMap.range (f.baseChange A) :=
    LinearMap.exact_iff.mp hex
  have hflat : Module.Flat A ((A ⊗[R] N) ⧸ LinearMap.range (f.baseChange A)) := by
    apply flat_cokernel_of_lTensor_injective
    intro Q _ _
    let : Module R Q := Module.compHom Q (algebraMap R A)
    let : IsScalarTower R A Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact lTensor_baseChange_injective f (hf Q)
  let : Module.Flat A ((A ⊗[R] N) ⧸ LinearMap.ker (q.baseChange A)) := hker.symm ▸ hflat
  exact Module.Flat.of_linearEquiv ((q.baseChange A).quotKerEquivOfSurjective hsurj).symm

/--
概要：左端が平坦で普遍単射なら、正則な境界上で余核の純変換の平坦性から中央の平坦性が従う。
方針：平坦な左端では境界ねじれが消えるので、純変換後の短完全列の両端が平坦になる。
規約：境界元は追加の基底変更先で正則とする。
使われ方：Stacks 0815 で、台の次元を下げた余核の帰納結果を元の加群へ戻す。
-/
theorem modulePureTransform_baseChange_flat_of_flat_source
    {R A M N P : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (a : A) (ha : IsRegular a) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Exact f g) (hg : Surjective g)
    (hf : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q], Injective (f.lTensor Q))
    [Module.Flat A (modulePureTransform a (A ⊗[R] P))] :
    Module.Flat A (modulePureTransform a (A ⊗[R] N)) := by
  let : Module.Flat A (modulePureTransform a (A ⊗[R] M)) :=
    Module.Flat.of_linearEquiv ((boundaryTorsion a (A ⊗[R] M)).quotEquivOfEqBot
      (boundaryTorsion_eq_bot_of_flat a (A ⊗[R] M) ha))
  exact modulePureTransform_baseChange_flat_of_flat_ends a f g hex hg hf

end SerrePositivity.AlgebraicGeometry
