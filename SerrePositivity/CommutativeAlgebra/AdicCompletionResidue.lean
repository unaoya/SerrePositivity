module

public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # 有限生成な極大イデアルに沿う完備化の剰余体

Mathlibの有限生成版の局所性・剰余体の保存を、指定体への同型と自然性へ接続する。
完備化される環のNoether性は不要。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
variable {S K : Type*} [CommRing S] [IsLocalRing S] [Field K]

/-- 完備化の剰余体を指定体へ同定する。 -/
noncomputable def adicCompletionTargetResidueEquiv
    (hfg : (maximalIdeal S).FG) (e : ResidueField S ≃+* K) :
    letI : IsLocalRing (AdicCompletion (maximalIdeal S) S) :=
      AdicCompletion.isLocalRing_of_fg hfg
    ResidueField (AdicCompletion (maximalIdeal S) S) ≃+* K := by
  let : IsLocalRing (AdicCompletion (maximalIdeal S) S) :=
    AdicCompletion.isLocalRing_of_fg hfg
  let : IsLocalHom (algebraMap S (AdicCompletion (maximalIdeal S) S)) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  exact (RingEquiv.ofBijective (ResidueField.map
    (algebraMap S (AdicCompletion (maximalIdeal S) S)))
    (AdicCompletion.residueField_map_bijective_of_fg hfg)).symm.trans e

/-- 元の環の元は、指定体で元の剰余体同型による値を持つ。 -/
theorem adicCompletionTargetResidueEquiv_apply
    (hfg : (maximalIdeal S).FG) (e : ResidueField S ≃+* K) (s : S) :
    letI : IsLocalRing (AdicCompletion (maximalIdeal S) S) :=
      AdicCompletion.isLocalRing_of_fg hfg
    adicCompletionTargetResidueEquiv hfg e
      (residue _ (algebraMap S (AdicCompletion (maximalIdeal S) S) s)) = e (residue S s) := by
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  let r : ResidueField S ≃+* ResidueField C := RingEquiv.ofBijective
    (ResidueField.map (algebraMap S C)) (AdicCompletion.residueField_map_bijective_of_fg hfg)
  change e (r.symm (residue C (algebraMap S C s))) = _
  rw [← ResidueField.map_residue (algebraMap S C)]
  change e (r.symm (r (residue S s))) = _
  rw [r.symm_apply_apply]

/-- 指定体への同型は、基底の剰余体からの係数写像とも両立する。 -/
theorem adicCompletionTargetResidueEquiv_base_map
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Algebra (ResidueField B) K]
    (hfg : (maximalIdeal S).FG) (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x)
    (x : ResidueField B) :
    let C := AdicCompletion (maximalIdeal S) S
    letI : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
    letI : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
    letI : IsLocalHom (algebraMap B C) := by
      rw [IsScalarTower.algebraMap_eq B S C]
      infer_instance
    adicCompletionTargetResidueEquiv hfg e (ResidueField.map (algebraMap B C) x) =
      algebraMap (ResidueField B) K x := by
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hfg
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
  change adicCompletionTargetResidueEquiv hfg e
    (ResidueField.map (algebraMap B C) (residue B b)) = _
  rw [ResidueField.map_residue, IsScalarTower.algebraMap_apply B S C,
    adicCompletionTargetResidueEquiv_apply, ← ResidueField.map_residue]
  exact he (residue B b)

end SerrePositivity
