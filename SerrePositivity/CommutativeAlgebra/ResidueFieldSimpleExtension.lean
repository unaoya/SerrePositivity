module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldAlgebraicExtension
public import SerrePositivity.CommutativeAlgebra.ResidueFieldTranscendentalExtension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # 単生成剰余体拡大の共通入口

代数的・超越的単生成拡大を一つの入口にまとめる。
係数体同型に沿った生成条件の移送も供給する。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 任意の単生成体拡大を剰余体として持つ平坦局所拡大を構成する。
代数的な場合はR1、超越的な場合はR2を適用する。 -/
theorem exists_flat_local_extension_of_simple_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (a : K) (hgen : IntermediateField.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (IsNoetherianRing B → IsNoetherianRing S) ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ s : S, e (residue S s) = a := by
  classical
  by_cases ha : IsAlgebraic (ResidueField B) a
  · let pb := PowerBasis.ofAdjoinSimpleEqTop ha.isIntegral hgen
    obtain ⟨S, sRing, sLocal, sAlg, sHom, sFree, sFinite, sFlat, hmax, e, he, s, hs⟩ :=
      exists_finite_free_local_extension_of_powerBasis B K pb
    refine ⟨S, sRing, sLocal, sAlg, sHom, sFlat, ?_, hmax, e, he, s, ?_⟩
    · intro h
      let : IsNoetherianRing B := h
      exact IsNoetherianRing.of_finite B S
    · simpa only [pb, PowerBasis.ofAdjoinSimpleEqTop_gen] using hs
  · exact exists_flat_local_extension_of_transcendental_generator B K a ha hgen

/-- 係数体の同型と両立する代数構造では、体生成の条件を移送できる。 -/
theorem adjoin_eq_top_of_scalar_equiv
    {F L K : Type*} [Field F] [Field L] [Field K] [Algebra F K] [Algebra L K]
    (e : F ≃+* L) (he : ∀ x, algebraMap F K x = algebraMap L K (e x))
    (s : Set K) (hs : IntermediateField.adjoin L s = ⊤) :
    IntermediateField.adjoin F s = ⊤ := by
  have hr : Set.range (algebraMap F K) = Set.range (algebraMap L K) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, (he y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, by rw [he, e.apply_symm_apply]⟩
  have h : (IntermediateField.adjoin F s).toSubfield =
      (IntermediateField.adjoin L s).toSubfield := by
    simp only [IntermediateField.adjoin_toSubfield, hr]
  apply top_unique
  intro x _
  change x ∈ (IntermediateField.adjoin F s).toSubfield
  rw [h, hs]
  trivial

/-- 単生成中間体そのものは、その標準生成元で生成される。 -/
theorem adjoin_simple_gen_eq_top
    (F K : Type*) [Field F] [Field K] [Algebra F K] (a : K) :
    IntermediateField.adjoin F {IntermediateField.AdjoinSimple.gen F a} = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin F {a}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]
  rw [Set.image_singleton]
  rfl

end SerrePositivity
