module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：始域の平坦なアフィン底変換は、基底に関する加群の平坦性を保存する。
方針：基底環上の単射を加群でテンソルし、その後に始域の環上でテンソルする。
規約：元の始域の環が基底上平坦であることは要求しない。
使われ方：Stacks 0814・0815 の始域 étale 近傍へ境界外の平坦性を移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：基底上平坦な加群を、始域の平坦な環写像で底変換しても基底上平坦。
方針：テンソル積の結合を変え、元の加群と始域の係数拡大を順に適用して単射性を保つ。
規約：基底の作用は始域を経由して与える。
使われ方：基底変更を含む étale 局所有限化で境界外の平坦性を保つ。
-/
theorem flat_tensor_of_flat_source_change
    {R B D M : Type*} [CommRing R] [CommRing B] [CommRing D] [Algebra R B]
    [Algebra R D] [Algebra B D] [IsScalarTower R B D] [Module.Flat B D]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Flat R M] :
    Module.Flat R (D ⊗[B] M) := by
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro A Z _ _ _ _ f hf
  let g := TensorProduct.AlgebraTensorModule.lTensor B M f
  let eA := TensorProduct.AlgebraTensorModule.assoc R B B D M A
  let eZ := TensorProduct.AlgebraTensorModule.assoc R B B D M Z
  let fD := TensorProduct.AlgebraTensorModule.lTensor B (D ⊗[B] M) f
  have hcomm : (g.lTensor D).comp eA.toLinearMap = eZ.toLinearMap.comp fD := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro z a
    induction z using TensorProduct.inductionOn with
    | tmul d m => rfl
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hD : Function.Injective ((g.lTensor D).comp eA.toLinearMap) :=
    (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp eA.injective
  rw [hcomm] at hD
  intro x y hxy
  apply hD
  exact congrArg eZ hxy

end SerrePositivity.AlgebraicGeometry
