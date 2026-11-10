module

public import SerrePositivity.AlgebraicGeometry.PureTransformFaithfullyFlatDescent
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
概要：有限個の平坦なアフィン被覆を通して加群と純変換の平坦性を降ろす。
方針：被覆環の有限積は忠実平坦なので、テンソルした単射性を反映する。
規約：加群の平坦性を測る基底環と、被覆する始域の環を区別する。
使われ方：Stacks 0814 の étale 始域被覆で純変換の平坦性を確かめる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem flat_pi_of_finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/--
概要：有限個の平坦なアフィン射で始域を覆い、各引き戻しが基底上平坦なら、元の加群も基底上平坦。
方針：被覆環の有限積へのテンソル積を各被覆へのテンソル積の積として扱う。
規約：被覆は始域の各素点に持ち上がりがあることとして入力する。
使われ方：étale 局所の平坦性を元の加群へ戻す。
-/
theorem flat_of_flat_tensor_affine_cover
    {R B M ι : Type u} [CommRing R] [CommRing B] [Algebra R B] [Finite ι]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    (D : ι → Type u) [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)]
    [∀ i, Algebra R (D i)] [∀ i, IsScalarTower R B (D i)] [∀ i, Module.Flat B (D i)]
    (hcover : ∀ q : PrimeSpectrum B, ∃ (i : ι) (t : PrimeSpectrum (D i)),
      t.comap (algebraMap B (D i)) = q)
    (hflat : ∀ i, Module.Flat R (D i ⊗[B] M)) :
    Module.Flat R M := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let C := ∀ i, D i
  let : Module.Flat B C := flat_pi_of_finite D
  let : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_comap_surjective (fun q => by
    obtain ⟨i, t, ht⟩ := hcover q
    refine ⟨t.comap (Pi.evalRingHom D i), ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    exact ht)
  let : ∀ i, Module.Flat R (D i ⊗[B] M) := hflat
  let : Module.Flat R (∀ i, D i ⊗[B] M) := flat_pi_of_finite fun i => D i ⊗[B] M
  let e := (TensorProduct.piLeft B M D).restrictScalars R
  let : Module.Flat R (C ⊗[B] M) := Module.Flat.of_linearEquiv e
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro A Z _ _ _ _ f hf
  let g := TensorProduct.AlgebraTensorModule.lTensor B M f
  let eA := TensorProduct.AlgebraTensorModule.assoc R B B C M A
  let eZ := TensorProduct.AlgebraTensorModule.assoc R B B C M Z
  let fC := TensorProduct.AlgebraTensorModule.lTensor B (C ⊗[B] M) f
  have hcomm : (g.lTensor C).comp eA.toLinearMap = eZ.toLinearMap.comp fC := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro z a
    induction z using TensorProduct.inductionOn with
    | tmul c m => rfl
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  have hinj : Function.Injective ((g.lTensor C).comp eA.toLinearMap) := by
    rw [hcomm]
    exact eZ.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap f hf)
  change Function.Injective g
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective B C g).mp
  intro x y hxy
  apply eA.symm.injective
  apply hinj
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hxy

/--
概要：平坦なアフィン被覆の各項で純変換が基底上平坦なら、元の純変換も基底上平坦。
方針：純変換と始域の平坦底変換を交換し、有限アフィン被覆で加群の平坦性を降下する。
規約：境界元は始域の環の元とし、境界ねじれが一様な冪で消えるとする。
使われ方：Stacks 0814 の共通中心の上で、étale 局所中心から元の純変換の平坦性を得る。
-/
theorem modulePureTransform_flat_of_flat_affine_cover
    {R B M ι : Type u} [CommRing R] [CommRing B] [Algebra R B] [Finite ι]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    (D : ι → Type u) [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)]
    [∀ i, Algebra R (D i)] [∀ i, IsScalarTower R B (D i)] [∀ i, Module.Flat B (D i)]
    (hcover : ∀ q : PrimeSpectrum B, ∃ (i : ι) (t : PrimeSpectrum (D i)),
      t.comap (algebraMap B (D i)) = q)
    (a : B) (n : ℕ) (hn : ∀ m ∈ boundaryTorsion a M, a ^ n • m = 0)
    (hflat : ∀ i, Module.Flat R (modulePureTransform (algebraMap B (D i) a) (D i ⊗[B] M))) :
    Module.Flat R (modulePureTransform a M) := by
  apply flat_of_flat_tensor_affine_cover D hcover
  intro i
  let : Module.Flat R (modulePureTransform (algebraMap B (D i) a) (D i ⊗[B] M)) := hflat i
  exact Module.Flat.of_linearEquiv
    ((pureTransformFlatCoefficientChangeEquivOfBound (S := D i) a n hn).restrictScalars R).symm

end SerrePositivity.AlgebraicGeometry
