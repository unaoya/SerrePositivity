module

public import SerrePositivity.AlgebraicGeometry.GenericFreeAtMinimalPrime
public import SerrePositivity.AlgebraicGeometry.GenericFlatness
public import SerrePositivity.AlgebraicGeometry.ValuativeOpenImageGenerizations

/-!
概要：極小素点集合が準コンパクトな被約環上の有限表示アフィン射の一般平坦性。
方針：各極小素点を自由な基本開で覆い、その和の内側に準コンパクト稠密開を選ぶ。
規約：基底の Noether 性や既約性を仮定しない。
使われ方：Rydh 3.7・3.10 における、非 Noether アフィン基底の一般平坦性の入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
private theorem flat_restrict_iSup_generic {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (V : ι → Y.Opens) (h : ∀ i, Flat (f ∣_ V i)) :
    Flat (f ∣_ ⨆ i, V i) := by
  let U := ⨆ i, V i
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Flat)
  intro x
  have hx : x.val ∈ (⨆ i, V i : Y.Opens) := x.property
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let W := U.ι ⁻¹ᵁ V i
  refine ⟨W, hi, ?_⟩
  have hW : U.ι ''ᵁ W = V i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_iSup V i)]
  rw [MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict f U W ≪≫ morphismRestrictEq f hW)]
  exact h i

set_option backward.isDefEq.respectTransparency false in
/-- 有限表示アフィン射は、全極小素点を含む準コンパクト稠密開上で平坦。
基底の被約性と極小素点集合の準コンパクト性のみを要求する。 -/
theorem exists_compact_dense_open_flat_restrict_specMap_of_finitePresentation
    (R B : CommRingCat.{u}) [IsReduced R] [Algebra R B] [Algebra.FinitePresentation R B]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}) :
    ∃ U : (Spec R).Opens, IsCompact U.carrier ∧ Dense U.carrier ∧
      (∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R → q ∈ U) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ U) := by
  let ι := {r : R // Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B)}
  let V (i : ι) : (Spec R).Opens := PrimeSpectrum.basicOpen i.1
  let W := ⨆ i, V i
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hMW (q : PrimeSpectrum R) (hq : q.asIdeal ∈ minimalPrimes R) : q ∈ W := by
    obtain ⟨r, hr, hf⟩ := exists_free_basicOpen_at_minimalPrime_of_finitePresentation R B hq
    exact (le_iSup V ⟨r, hf⟩) hr
  have hflat (i : ι) : Flat (f ∣_ V i) := by
    let : Module.Free (Localization.Away i.1) (Localization.Away i.1 ⊗[R] B) := i.2
    rw [MorphismProperty.arrow_mk_iso_iff @Flat
      (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) i.1), Flat.SpecMap_iff]
    change (Localization.awayMap (algebraMap R B) i.1).Flat
    let := SerrePositivity.GenericEtale.awayAlgebra R B i.1
    change Module.Flat (Localization.Away i.1) (Localization.Away (algebraMap R B i.1))
    exact Module.Flat.of_linearEquiv
      (SerrePositivity.originalAwayTensorEquiv R B i.1).symm.toLinearEquiv
  have : Flat (f ∣_ W) := flat_restrict_iSup_generic f V hflat
  obtain ⟨U, hUc, hUd, hUW, hMU⟩ :=
    exists_compact_denseOpen_of_contains_minimalPrimes R hmin W hMW
  refine ⟨U, hUc, hUd, hMU, ?_⟩
  let T := W.ι ⁻¹ᵁ U
  have hT : W.ι ''ᵁ T = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUW]
  have ht : Flat ((f ∣_ W) ∣_ T) := inferInstance
  rw [MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict f W T ≪≫ morphismRestrictEq f hT)] at ht
  exact ht

end SerrePositivity.AlgebraicGeometry
