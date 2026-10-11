module

public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.RingTheory.Flat.Stability

/-! # 平坦な基底変更と Koszul ホモロジー

平坦性によりホモロジーと係数拡大を交換する。環の押し出しで得た代数では、
係数拡大後のホモロジーを、底環からのテンソル積としても表す。
有限性・正則性・長さの条件は、この同型の構成には不要である。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits TensorProduct

set_option backward.isDefEq.respectTransparency false

/-- 平坦な係数拡大は、任意の複体のホモロジーと可換である。 -/
noncomputable def flatBaseChangeHomologyEquiv
    (T B : Type u) [CommRing T] [CommRing B] [Algebra T B] [Module.Flat T B]
    (K : CochainComplex (ModuleCat.{u} T) ℤ) (i : ℤ) :
    (baseChange (algebraMap T B) K).homology i ≃ₗ[B] B ⊗[T] K.homology i := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap T B)
  let : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ((K.sc i).mapHomologyIso F).toLinearEquiv.trans
    (extendScalarsObjEquivTensor T B (K.homology i))

/-- 平坦な係数拡大に関する Koszul ホモロジーの同型。 -/
noncomputable def flatBaseChangeKoszulHomologyEquiv
    (T B : Type u) [CommRing T] [CommRing B] [Algebra T B] [Module.Flat T B]
    {r : ℕ} (x : Fin r → T) (i : ℤ) :
    (koszulComplex (algebraMap T B ∘ x)).homology i ≃ₗ[B]
      B ⊗[T] (koszulComplex x).homology i :=
  (((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (baseChangeKoszulIso (algebraMap T B) x).symm).toLinearEquiv).trans
      (flatBaseChangeHomologyEquiv T B (koszulComplex x) i)

/-- 平坦な環拡大の押し出しも平坦である。 -/
theorem flat_of_algebra_isPushout
    (S R T B : Type u) [CommRing S] [CommRing R] [CommRing T] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R B] [Algebra T B] [Algebra S B]
    [IsScalarTower S R B] [IsScalarTower S T B] [Algebra.IsPushout S R T B]
    [Module.Flat S R] : Module.Flat T B := by
  let : Algebra.IsPushout S T R B := Algebra.IsPushout.symm inferInstance
  exact Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv S T R B).symm.toLinearEquiv

/-- 押し出し `B = R ⊗_S T` で、Koszul ホモロジーを `R ⊗_S H` と同定する。
`R` の `S` 上の平坦性だけでよく、`T` の平坦性は要求しない。 -/
noncomputable def pushoutKoszulHomologyEquiv
    (S R T B : Type u) [CommRing S] [CommRing R] [CommRing T] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R B] [Algebra T B] [Algebra S B]
    [IsScalarTower S R B] [IsScalarTower S T B] [Algebra.IsPushout S R T B]
    [Module.Flat S R] {r : ℕ} (x : Fin r → T) (i : ℤ) :
    letI := Module.compHom ((koszulComplex (algebraMap T B ∘ x)).homology i)
      (algebraMap R B)
    letI := Module.compHom ((koszulComplex x).homology i) (algebraMap S T)
    (koszulComplex (algebraMap T B ∘ x)).homology i ≃ₗ[R]
      R ⊗[S] (koszulComplex x).homology i := by
  let := flat_of_algebra_isPushout S R T B
  let M := (koszulComplex x).homology i
  let N := (koszulComplex (algebraMap T B ∘ x)).homology i
  let : Module S M := Module.compHom M (algebraMap S T)
  let : IsScalarTower S T M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R N := Module.compHom N (algebraMap R B)
  let : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact ((flatBaseChangeKoszulHomologyEquiv T B x i).restrictScalars R).trans
    (Algebra.IsPushout.cancelBaseChange S R T B M)

end SerrePositivity
