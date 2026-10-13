module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionNoetherian
public import SerrePositivity.CommutativeAlgebra.AdicCompletionResidue
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability

/-! # 指定剰余体を保持するNoether局所拡大の完備化

構成済みの平坦局所拡大を完備化し、極大イデアルの等式、剰余体同型の自然性、
指定した元の対応を保持する。代数的・超越的単生成拡大の共通の最終段階。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 平坦Noether局所拡大を完備化し、指定剰余体と生成元の対応を移送する。
Noether性を要求するのは完備化されるSであり、基底BのNoether性は不要。 -/
theorem exists_complete_flat_local_extension_with_residue
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x)
    (a : K) (s : S) (hs : e (residue S s) = a) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ eC : ResidueField C ≃+* K,
        (∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x) ∧
        ∃ c : C, eC (residue C c) = a := by
  let C := AdicCompletion (maximalIdeal S) S
  let : IsScalarTower B S C := inferInstance
  let : IsNoetherianRing C := isNoetherianRing_adicCompletion S (maximalIdeal S)
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  let : Module.Flat B C := Module.Flat.trans B S C
  have hcmax : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C := by
    rw [IsScalarTower.algebraMap_eq B S C, ← Ideal.map_map, hmax]
    exact AdicCompletion.maximalIdeal_eq_map.symm
  let eC : ResidueField C ≃+* K :=
    adicCompletionTargetResidueEquiv (maximalIdeal S).fg_of_isNoetherianRing e
  have hev (t : S) : eC (residue C (algebraMap S C t)) = e (residue S t) :=
    adicCompletionTargetResidueEquiv_apply (maximalIdeal S).fg_of_isNoetherianRing e t
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcmax, eC, ?_, algebraMap S C s, ?_⟩
  · exact adicCompletionTargetResidueEquiv_base_map
      (maximalIdeal S).fg_of_isNoetherianRing e he
  · rw [hev]
    exact hs
end SerrePositivity
