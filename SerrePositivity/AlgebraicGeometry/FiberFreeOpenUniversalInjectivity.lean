module

public import SerrePositivity.AlgebraicGeometry.FiberCokernelFromFreeOpen
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：閉ファイバーと交わる自由化主開から普遍単射を得る。
方針：主開上の平坦な加群への合成を閉ファイバーの生成点で調べる。
規約：基底は局所環とし、写像の始域は基底上射影とする。
使われ方：Stacks 0815 の余核による帰納の普遍単射性。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：整な閉ファイバーと交わる主開で平坦な標的に同型となる写像は、局所基底上で普遍単射。
方針：標的の主局所化は基底上平坦で、生成点で元の標的と一致する。
規約：主局所化上の標的は自由とし、生成点は閉ファイバー環の分数体で扱う。
使われ方：Stacks 0815 で、自由化写像の余核に台の次元による帰納を適用する。
-/
theorem lTensor_injective_of_away_bijective_at_closedFiber
    {R B M N : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Module.Projective R M] [Module.Flat B M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    [IsDomain (B ⊗[R] IsLocalRing.ResidueField R)]
    (f : M →ₗ[B] N) (b : B)
    (hb : algebraMap B (B ⊗[R] IsLocalRing.ResidueField R) b ≠ 0)
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)]
    (hf : Function.Bijective (f.baseChange (Localization.Away b)))
    (Q : Type v) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((f.restrictScalars R).lTensor Q) := by
  let A := B ⊗[R] IsLocalRing.ResidueField R
  let K := (⊥ : Ideal A).ResidueField
  let L := Localization.Away b
  let P := L ⊗[B] N
  let g : N →ₗ[B] P := TensorProduct.mk B L N 1
  let : Module.Flat B L := IsLocalization.flat L (Submonoid.powers b)
  let : Module.Flat R L := Module.Flat.trans R B L
  let : Module.Flat R P := Module.Flat.trans R L P
  have hbK : IsUnit (algebraMap B K b) := by
    rw [IsScalarTower.algebraMap_apply B A K]
    refine isUnit_iff_ne_zero.mpr fun h => hb ((IsFractionRing.injective A K) ?_)
    simpa only [map_zero] using h
  let j : L →+* K := IsLocalization.Away.lift b hbK
  let : Algebra L K := j.toAlgebra
  let : IsScalarTower B L K :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp b hbK).symm
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange B L K K N).symm.trans
    (TensorProduct.equivOfCompatibleSMul B L K K P)
  have hgK : g.baseChange K = e.toLinearMap := by
    ext x
    change g.baseChange K ((1 : K) ⊗ₜ[B] x) = e ((1 : K) ⊗ₜ[B] x)
    rw [LinearMap.baseChange_tmul]
    change (1 : K) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] x) = _
    simp only [e, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    rfl
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange B A K K N
  let eP := TensorProduct.AlgebraTensorModule.cancelBaseChange B A K K P
  have hcomm : ⇑(g.baseChange K) ∘ ⇑eN = ⇑eP ∘ ⇑((g.baseChange A).baseChange K) :=
    congrArg DFunLike.coe
      (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange B A K (M := K) g)
  have hg : Function.Injective ((g.baseChange A).lTensor K) := by
    change Function.Injective ((g.baseChange A).baseChange K)
    apply Function.Injective.of_comp (f := eP)
    rw [← hcomm, hgK]
    exact e.injective.comp eN.injective
  apply lTensor_injective_of_genericFiber_composite_injective f g _ Q
  rw [LinearMap.baseChange_comp, LinearMap.lTensor_comp]
  exact hg.comp (bijective_genericFiber_baseChange_of_away f b hb hf).injective

end SerrePositivity.AlgebraicGeometry
