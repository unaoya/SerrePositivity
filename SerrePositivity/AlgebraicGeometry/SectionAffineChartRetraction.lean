module

public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover
public import Mathlib.AlgebraicGeometry.Restrict
public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients
public import SerrePositivity.HomologicalAlgebra.Cech.Split

/-!
概要：元の切断をアフィン開へ制限し、切断環と完全化のČech完全性を得る。
方針：同じ制限の合成を確認し、Frobeniusの合成則とB1の切断の完全性を使う。
規約：選んだ開と元の構造射・切断を保持する。
使われ方：切断に適合する局所のČech計算（承認済み計画F02・F03）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の切断のアフィン開への制限は、同じ切断環の射のretractionを与える。 -/
theorem section_affine_chart_retraction
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (U : Y.Opens) (hU : IsAffineOpen U)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hVs : V ≤ s ⁻¹ᵁ U) :
    ∃ r : Γ((U ⊓ g ⁻¹ᵁ V).toScheme, ⊤) ⟶ Γ(V.toScheme, ⊤),
      (g.resLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right).appTop ≫ r = 𝟙 _ := by
  have hV : V ≤ s ⁻¹ᵁ (U ⊓ g ⁻¹ᵁ V) := by
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]
    exact le_inf hVs le_rfl
  let r := s.resLE (U ⊓ g ⁻¹ᵁ V) V hV
  have hr : r ≫ g.resLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right = 𝟙 _ := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    dsimp only [r]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      hs, Category.comp_id, Category.id_comp]
  refine ⟨r.appTop, ?_⟩
  rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]

/-- 同じ局所の切断環のretractionから、実際のFrobenius係数のČech完全性を得る。 -/
theorem section_affine_chart_frobeniusCechExact
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (U : Y.Opens) (hU : IsAffineOpen U)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hVs : V ≤ s ⁻¹ᵁ U) (p : ℕ) (hp : p.Prime)
    (hz : (p : Γ(V.toScheme, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk (g.resLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right).appTop) p hp hz) := by
  obtain ⟨r, hr⟩ := section_affine_chart_retraction g s hs U hU V hV hVs
  let q := (g.resLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right).appTop
  have hq : r.hom.comp q.hom = RingHom.id _ := congrArg CommRingCat.Hom.hom hr
  have hW : (p : Γ((U ⊓ g ⁻¹ᵁ V).toScheme, ⊤)) = 0 := by
    rw [← map_natCast q.hom, hz, map_zero]
  apply (frobeniusAugmentedRingCoefficients_exact_iff (Arrow.mk q) p hp hz hW).mpr
  apply SerrePositivity.Cech.isCechExact_of_retraction _
    (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hW hz r.hom))
  apply CommRingCat.hom_ext
  change (frobeniusDirectLimitMap p hp hW hz r.hom).comp
    (frobeniusDirectLimitMap p hp hz hW q.hom) = RingHom.id _
  rw [frobeniusDirectLimitMap_comp, hq, frobeniusDirectLimitMap_id]

end SerrePositivity.AlgebraicGeometry
