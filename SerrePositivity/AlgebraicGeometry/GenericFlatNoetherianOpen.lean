module

public import SerrePositivity.AlgebraicGeometry.GenericFlatCommonCoefficients
public import SerrePositivity.AlgebraicGeometry.GenericFlatness

/-!
概要：一般自由な有限個の基本開を、幾何の平坦開へ移す。
方針：Spec の主開・局所化・tensor の既存比較と、平坦性の開上の局所性を使う。
規約：この比較そのものには係数環の Noether 性は不要。
使われ方：Noether 係数模型を平坦化する指定開の供給。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u v

set_option backward.isDefEq.respectTransparency false in
/-- 開上の平坦性を、和の開へ貼り合わせる。 -/
theorem flat_restrict_iSup_of_flat_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type v} (V : ι → Y.Opens) (h : ∀ i, Flat (f ∣_ V i)) :
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
/-- 有限個の基本開上の自由性から、その和での構造射の平坦性を得る。 -/
theorem flat_restrict_iSup_basicOpen_of_free_tensor
    (A S : CommRingCat.{u}) [Algebra A S] {n : ℕ} (t : Fin n → A)
    (hfree : ∀ i, Module.Free (Localization.Away (t i))
      (Localization.Away (t i) ⊗[A] S)) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A S)) ∣_
      ⨆ i, PrimeSpectrum.basicOpen (t i)) := by
  apply flat_restrict_iSup_of_flat_restrict
  intro i
  let : Module.Free (Localization.Away (t i))
    (Localization.Away (t i) ⊗[A] S) := hfree i
  rw [MorphismProperty.arrow_mk_iso_iff @Flat
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap A S)) (t i)), Flat.SpecMap_iff]
  change (Localization.awayMap (algebraMap A S) (t i)).Flat
  let := SerrePositivity.GenericEtale.awayAlgebra A S (t i)
  change Module.Flat (Localization.Away (t i)) (Localization.Away (algebraMap A S (t i)))
  exact Module.Flat.of_linearEquiv
    (SerrePositivity.originalAwayTensorEquiv A S (t i)).symm.toLinearEquiv

end SerrePositivity.AlgebraicGeometry
