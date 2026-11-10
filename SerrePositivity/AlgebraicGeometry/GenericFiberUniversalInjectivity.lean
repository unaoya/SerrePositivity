module

public import SerrePositivity.AlgebraicGeometry.ResidueTensorUniversalInjectivity
public import SerrePositivity.AlgebraicGeometry.FiberSupportDimension
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：整な閉ファイバーの生成点での単射性を、基底環上の普遍単射性に移す。
方針：閉ファイバー上の平坦な始域を分数体に埋め込み、剰余体での単射性を使う。
規約：標的を生成点の近くの平坦な加群へ写す形で述べる。
使われ方：Stacks 05I3 と 0815 の、生成点で基底を与える写像の余核による帰納。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private def fractionTensorMap (A V : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup V] [Module A V] : V →ₗ[A] (⊥ : Ideal A).ResidueField ⊗[A] V :=
  ((Algebra.linearMap A (⊥ : Ideal A).ResidueField).rTensor V).comp
    (TensorProduct.lid A V).symm.toLinearMap

private def fiberBaseChangeEquiv (R S k V : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing k] [Algebra R k] [AddCommGroup V] [Module R V] [Module S V]
    [IsScalarTower R S V] : k ⊗[R] V ≃ₗ[R] (S ⊗[R] k) ⊗[S] V :=
  (TensorProduct.comm R k V).trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S V k).symm.trans
      (TensorProduct.comm S V (S ⊗[R] k))).restrictScalars R)

/--
概要：整な底変換ファイバーの生成点で単射なら、そのファイバー全体への底変換でも単射。
方針：始域の平坦性で分数体への写像の単射性を得て、テンソル積を比較する。
規約：ファイバーを与える係数環は代数として入力する。
使われ方：各剰余体での単射性を大域の普遍単射性に渡す。
-/
theorem lTensor_injective_of_genericFiber_injective
    {R S k M N : Type*} [CommRing R] [CommRing S] [CommRing k] [Algebra R S] [Algebra R k]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat S M] [IsDomain (S ⊗[R] k)] (f : M →ₗ[S] N)
    (h : Function.Injective ((f.baseChange (S ⊗[R] k)).lTensor
      ((⊥ : Ideal (S ⊗[R] k)).ResidueField))) :
    Function.Injective ((f.restrictScalars R).lTensor k) := by
  let A := S ⊗[R] k
  let K := (⊥ : Ideal A).ResidueField
  let α := f.baseChange A
  have hj : Function.Injective (fractionTensorMap A (A ⊗[S] M)) :=
    (Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap A K)
      (IsFractionRing.injective A K)).comp (TensorProduct.lid A (A ⊗[S] M)).symm.injective
  have hα : Function.Injective α := by
    apply Function.Injective.of_comp (f := fractionTensorMap A (A ⊗[S] N))
    have hcomp : (fractionTensorMap A (A ⊗[S] N)).comp α =
        (α.lTensor K).comp (fractionTensorMap A (A ⊗[S] M)) := by
      ext x
      simp [fractionTensorMap]
    rw [← LinearMap.coe_comp, hcomp]
    exact h.comp hj
  let eM := fiberBaseChangeEquiv R S k M
  let eN := fiberBaseChangeEquiv R S k N
  have hcomp : eN.toLinearMap.comp ((f.restrictScalars R).lTensor k) =
      (α.restrictScalars R).comp eM.toLinearMap := by
    ext a m
    simp [fiberBaseChangeEquiv, eM, eN, α]
  apply Function.Injective.of_comp (f := eN)
  change Function.Injective ⇑(eN.toLinearMap.comp ((f.restrictScalars R).lTensor k))
  rw [hcomp]
  exact hα.comp eM.injective

/--
概要：局所基底上の写像が整な閉ファイバーの生成点で平坦な標的への単射を与えるなら、
元の写像は基底上で普遍単射。
方針：閉ファイバー上の始域が平坦なら分数体への写像が単射であり、
剰余体での単射性から基底環上の任意のテンソル積に移る。
規約：生成点での比較は閉ファイバー代数の分数体を用いる。
使われ方：滑らかな正規化先の生成点で自由加群を有限加群から切り出す。
-/
theorem lTensor_injective_of_genericFiber_composite_injective
    {R S M N P : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [Module.Projective R M] [Module.Flat S M] [Module.Flat R P]
    [IsDomain (S ⊗[R] IsLocalRing.ResidueField R)]
    (f : M →ₗ[S] N) (g : N →ₗ[S] P)
    (h : Function.Injective (((g.comp f).baseChange (S ⊗[R] IsLocalRing.ResidueField R)).lTensor
      ((⊥ : Ideal (S ⊗[R] IsLocalRing.ResidueField R)).ResidueField)))
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((f.restrictScalars R).lTensor Q) := by
  have hk := lTensor_injective_of_genericFiber_injective (g.comp f) h
  have hQ := lTensor_injective_of_residueTensor_injective_of_projective
    ((g.comp f).restrictScalars R) hk Q
  rw [LinearMap.restrictScalars_comp, LinearMap.lTensor_comp] at hQ
  exact Function.Injective.of_comp (f := (g.restrictScalars R).lTensor Q)
    (g := (f.restrictScalars R).lTensor Q) hQ

/--
概要：整な底変換ファイバーの生成点で全射になる写像の余核は、
ファイバー上で台の次元が一つ以上小さい。
方針：底変換が余核を保つことを右完全性で示し、生成点での消滅を使う。
規約：ファイバーへの底変換を一般の整域への底変換として述べる。
使われ方：Stacks 0815 で帰納の対象となる加群のファイバー次元を評価する。
-/
theorem supportDim_baseChange_cokernel_add_one_le
    {S A M N : Type*} [CommRing S] [CommRing A] [Algebra S A] [IsDomain A]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (f : M →ₗ[S] N)
    (hf : Function.Surjective ((f.baseChange A).lTensor (⊥ : Ideal A).ResidueField)) :
    Module.supportDim A (A ⊗[S] (N ⧸ LinearMap.range f)) + 1 ≤ ringKrullDim A := by
  let q := (LinearMap.range f).mkQ
  have hq : Function.Surjective (q.baseChange A) :=
    q.lTensor_surjective A (Submodule.mkQ_surjective _)
  have hex : Function.Exact (f.baseChange A) (q.baseChange A) :=
    lTensor_exact A (LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)) (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker (q.baseChange A) = LinearMap.range (f.baseChange A) :=
    LinearMap.exact_iff.mp hex
  let e := (q.baseChange A).quotKerEquivOfSurjective hq
  rw [← Module.supportDim_eq_of_equiv e, hker]
  exact supportDim_cokernel_add_one_le_of_generic_surjective (f.baseChange A) hf

end SerrePositivity.AlgebraicGeometry
