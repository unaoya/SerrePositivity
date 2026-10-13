module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionResidue
public import SerrePositivity.CommutativeAlgebra.AdicCompletionFlatQuotient
public import SerrePositivity.CommutativeAlgebra.ResidueFieldGeneralExtension

/-! # 任意剰余体拡大の完備局所実現と冪商の平坦性

非Noetherであり得る中間環を有限生成な極大イデアルに沿って完備化する。
完備性・局所性・極大イデアル・剰余体・全冪商の平坦性を実際に供給する。
完備化全体のNoether性と基底上の平坦性は、まだこの定理の結論ではない。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u

/-- 有限生成な基底の極大イデアルを持つ平坦局所拡大を完備化する。
元の拡大環SのNoether性を要求しない。 -/
theorem exists_complete_local_extension_with_flat_quotients
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hB : (maximalIdeal B).FG)
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧ (maximalIdeal C).FG ∧
      (∀ n : ℕ, Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (C ⧸ ((maximalIdeal B) ^ n).map (algebraMap B C))) ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  have hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  let : IsAdicComplete (maximalIdeal C) C := AdicCompletion.isAdicComplete_of_fg hS
  have hcmax : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C := by
    rw [IsScalarTower.algebraMap_eq B S C, ← Ideal.map_map, hmax]
    exact (AdicCompletion.maximalIdeal_eq_map_of_fg hS).symm
  have hcFG : (maximalIdeal C).FG := hcmax ▸ hB.map (algebraMap B C)
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hcmax, hcFG, ?_, adicCompletionTargetResidueEquiv hS e, ?_⟩
  · intro n
    exact Eq.mp (congrArg (fun J : Ideal S ↦
      Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (AdicCompletion J S ⧸ ((maximalIdeal B) ^ n).map
          (algebraMap B (AdicCompletion J S)))) hmax)
      (adicCompletionBasePowQuotient_flat (S := S) (maximalIdeal B) hB n)
  · exact adicCompletionTargetResidueEquiv_base_map hS e he

/-- 任意の指定剰余体拡大に対し、完備局所実現と全冪商の平坦性を実構成する。
Noether基底を使うのは、その極大イデアルの有限生成性の供給だけ。
結論にCのNoether性・B上の平坦性を加える二つの判定は、別の証明課題。 -/
theorem exists_complete_local_extension_of_residueField_with_flat_quotients
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧ (maximalIdeal C).FG ∧
      (∀ n : ℕ, Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (C ⧸ ((maximalIdeal B) ^ n).map (algebraMap B C))) ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_flat_local_extension_of_residueField (B := B) (K := K)
  exact exists_complete_local_extension_with_flat_quotients B S K
    (maximalIdeal B).fg_of_isNoetherianRing hmax e he

end SerrePositivity
