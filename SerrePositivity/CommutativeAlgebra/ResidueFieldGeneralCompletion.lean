module

public import SerrePositivity.CommutativeAlgebra.AdicNoetherianCriterion
public import SerrePositivity.CommutativeAlgebra.AdicCompletionFlat
public import SerrePositivity.CommutativeAlgebra.AdicCompletionResidue
public import SerrePositivity.CommutativeAlgebra.AdicCompletionFlatQuotient
public import SerrePositivity.CommutativeAlgebra.ResidueFieldGeneralExtension

/-! # 任意剰余体拡大の完備Noether平坦局所実現

非Noetherであり得る中間環を有限生成な極大イデアルに沿って完備化する。
完備性・局所性・極大イデアル・剰余体・全冪商の平坦性を実際に供給する。
完備局所環のNoether性は一般判定を適用して供給する。基底上の平坦性は共通の代数版の平坦性を同じCへ適用して供給する。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u

/-- 構成する完備化Cそのものについて、Noether性・完備性・剰余体・冪商を確認する。
存在定理からCの由来を推測せず、同じCに共通の平坦性を適用できる入口。 -/
theorem adicCompletion_local_residue_properties
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hB : (maximalIdeal B).FG)
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) :
    let hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
    let C := AdicCompletion (maximalIdeal S) S
    letI : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
    letI : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
    letI : IsLocalHom (algebraMap B C) := by
      rw [IsScalarTower.algebraMap_eq B S C]
      infer_instance
    IsNoetherianRing C ∧ IsAdicComplete (maximalIdeal C) C ∧
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
  let : IsNoetherianRing C := isNoetherianRing_of_complete_local_of_fg C hcFG
  refine ⟨inferInstance, inferInstance, hcmax, hcFG, ?_,
    adicCompletionTargetResidueEquiv hS e, ?_⟩
  · intro n
    exact Eq.mp (congrArg (fun J : Ideal S ↦
      Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (AdicCompletion J S ⧸ ((maximalIdeal B) ^ n).map
          (algebraMap B (AdicCompletion J S)))) hmax)
      (adicCompletionBasePowQuotient_flat (S := S) (maximalIdeal B) hB n)
  · exact adicCompletionTargetResidueEquiv_base_map hS e he

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
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
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
  obtain ⟨hNoeth, hComplete, hcmax, hcFG, hquot, eC, heC⟩ :=
    adicCompletion_local_residue_properties B S K hB hmax e he
  exact ⟨C, inferInstance, inferInstance, hNoeth, hComplete, inferInstance, inferInstance,
    hcmax, hcFG, hquot, eC, heC⟩

/-- 任意の指定剰余体拡大に対し、完備局所実現と全冪商の平坦性を実構成する。
Noether基底を使うのは、その極大イデアルの有限生成性の供給だけ。
CのNoether性は証明済み。この入口は冪商の情報を保持する。環全体の平坦性を含む最終入口も下で供給する。 -/
theorem exists_complete_local_extension_of_residueField_with_flat_quotients
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
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

/-- Noether基底上の平坦局所拡大の具体的な完備化に、共通の代数版の平坦性を適用する。
中間環SのNoether性や基底Bの完備性は要求しない。 -/
theorem exists_complete_flat_local_extension_of_noetherian_base
    (B S K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  have hB := (maximalIdeal B).fg_of_isNoetherianRing
  have hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  obtain ⟨hNoeth, hComplete, hcmax, hcFG, hquot, eC, heC⟩ :=
    adicCompletion_local_residue_properties B S K hB hmax e he
  have hFlat : Module.Flat B C := Eq.mp
    (congrArg (fun J : Ideal S ↦ Module.Flat B (AdicCompletion J S)) hmax)
    (flat_adicCompletion_algebra_of_flat (S := S) (maximalIdeal B))
  exact ⟨C, inferInstance, inferInstance, hNoeth, hComplete, inferInstance, inferInstance,
    hFlat, hcmax, eC, heC⟩

/-- 任意の剰余体拡大を、同じ宇宙の完備Noether平坦局所拡大で実現する。
基底の完備性や体拡大の有限性・分離性・完全性は仮定しない。 -/
theorem exists_complete_flat_local_extension_of_residueField
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_flat_local_extension_of_residueField (B := B) (K := K)
  exact exists_complete_flat_local_extension_of_noetherian_base B S K hmax e he

end SerrePositivity
