module

public import SerrePositivity.AlgebraicGeometry.GenericFiberUniversalInjectivity
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：自由化する主開が整なファイバーと交わるなら、余核の台の次元がそのファイバーで下がる。
方針：ファイバーの分数体では主開の元を反転できるので、主開上の同型を生成点へ移す。
規約：ファイバーの環は代数として与え、主開の元の像が非零と仮定する。
使われ方：Stacks 0815 の余核による次元帰納。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct
open Module TensorProduct

/--
概要：主開上で自由な有限加群には、元の加群の有限個の元で与えられ、主開上で同型になる写像がある。
方針：主開上の基底ベクトルごとに分母を払い、基底を単元倍して元の加群の像に入れる。
規約：自由な始域は有限台関数の加群とする。
使われ方：自由化主開で選んだ写像を各ファイバーの生成点で使う。
-/
theorem exists_finite_free_map_bijective_away
    {B N : Type u} [CommRing B] [AddCommGroup N] [Module B N] [Module.Finite B N]
    (b : B) [Nontrivial (Localization.Away b)]
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)] :
    ∃ (ι : Type u) (_ : Finite ι) (f : (ι →₀ B) →ₗ[B] N),
      Function.Bijective (f.baseChange (Localization.Away b)) := by
  classical
  let C := Localization.Away b
  let I := Module.Free.ChooseBasisIndex C (C ⊗[B] N)
  let β : Basis I C (C ⊗[B] N) := Module.Free.chooseBasis C (C ⊗[B] N)
  let : Finite I := Module.Finite.finite_basis β
  let j : N →ₗ[B] C ⊗[B] N := TensorProduct.mk B C N 1
  have h (i : I) : ∃ (m : N) (u : Cˣ), j m = (u : C) • β i := by
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers b) j (β i)
    let hu := IsLocalization.map_units C s
    refine ⟨m, hu.unit, ?_⟩
    rw [IsUnit.unit_spec hu, IsScalarTower.algebraMap_smul]
    exact hs.symm
  choose m u hm using h
  let f : (I →₀ B) →ₗ[B] N := Finsupp.linearCombination B m
  let α : Basis I C (C ⊗[B] (I →₀ B)) := Finsupp.basisSingleOne.baseChange C
  let e := α.equiv (β.unitsSMul u) (Equiv.refl I)
  have he : f.baseChange C = e.toLinearMap := by
    apply α.ext
    intro i
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply]
    simp only [α, Basis.baseChange_apply, Finsupp.coe_basisSingleOne, Units.smul_def]
    change f.baseChange C ((1 : C) ⊗ₜ[B] Finsupp.single i 1) = (u i : C) • β i
    rw [LinearMap.baseChange_tmul, show f (Finsupp.single i 1) = m i by simp [f]]
    exact hm i
  refine ⟨I, inferInstance, f, ?_⟩
  rw [he]
  exact e.bijective

private theorem bijective_baseChange_iff_iterated
    {B C K M N : Type*} [CommRing B] [CommRing C] [CommRing K]
    [Algebra B C] [Algebra B K] [Algebra C K] [IsScalarTower B C K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) :
    Function.Bijective (f.baseChange K) ↔
      Function.Bijective ((f.baseChange C).baseChange K) := by
  let eM := AlgebraTensorModule.cancelBaseChange B C K K M
  let eN := AlgebraTensorModule.cancelBaseChange B C K K N
  have h : ⇑(f.baseChange K) ∘ ⇑eM = ⇑eN ∘ ⇑((f.baseChange C).baseChange K) :=
    congrArg DFunLike.coe (AlgebraTensorModule.lTensor_comp_cancelBaseChange B C K (M := K) f)
  rw [← Function.Bijective.of_comp_iff _ eM.bijective, h,
    Function.Bijective.of_comp_iff' eN.bijective]

/--
概要：写像が主開上で同型なら、その主開と交わる整なファイバーの生成点でも同型。
方針：ファイバーの分数体への写像を主局所化経由にして、二段階のテンソル積を一段階にする。
規約：生成点の体は零素イデアルの剰余体で表す。
使われ方：生成点で普遍単射性と余核の次元降下を得る。
-/
theorem bijective_genericFiber_baseChange_of_away
    {B A M N : Type*} [CommRing B] [CommRing A] [Algebra B A] [IsDomain A]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (b : B) (hb : algebraMap B A b ≠ 0)
    (hf : Function.Bijective (f.baseChange (Localization.Away b))) :
    Function.Bijective ((f.baseChange A).lTensor (⊥ : Ideal A).ResidueField) := by
  let K := (⊥ : Ideal A).ResidueField
  let C := Localization.Away b
  have hbK : IsUnit (algebraMap B K b) := by
    rw [IsScalarTower.algebraMap_apply B A K]
    refine isUnit_iff_ne_zero.mpr fun h => hb ((IsFractionRing.injective A K) ?_)
    simpa only [map_zero] using h
  let j : C →+* K := IsLocalization.Away.lift b hbK
  let : Algebra C K := j.toAlgebra
  let : IsScalarTower B C K :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp b hbK).symm
  have hc : Function.Bijective ((f.baseChange C).baseChange K) :=
    ((LinearEquiv.ofBijective (f.baseChange C) hf).lTensor K).bijective
  exact (bijective_baseChange_iff_iterated (C := A) (K := K) f).mp
    ((bijective_baseChange_iff_iterated (C := C) (K := K) f).mpr hc)

/--
概要：自由化主開が整なファイバーと交わると、そのファイバーで余核の台の次元が一つ以上下がる。
方針：主開での同型を生成点に移し、生成点で余核が消えることを使う。
規約：余核は値域による商で表す。
使われ方：同じ自由化写像を用いて各ファイバーの次元を一様に下げる。
-/
theorem supportDim_baseChange_cokernel_add_one_le_of_away_bijective
    {B A M N : Type*} [CommRing B] [CommRing A] [Algebra B A] [IsDomain A]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module.Finite B N]
    (f : M →ₗ[B] N) (b : B) (hb : algebraMap B A b ≠ 0)
    (hf : Function.Bijective (f.baseChange (Localization.Away b))) :
    Module.supportDim A (A ⊗[B] (N ⧸ LinearMap.range f)) + 1 ≤ ringKrullDim A :=
  supportDim_baseChange_cokernel_add_one_le f
    (bijective_genericFiber_baseChange_of_away f b hb hf).surjective

end SerrePositivity.AlgebraicGeometry
