module

public import SerrePositivity.AlgebraicGeometry.ValuationSpecializationDiagram
public import SerrePositivity.AlgebraicGeometry.SchemeVCover

/-!
概要：スキームの v 判定から、特殊化の鎖の同時持ち上げを得る。
方針：鎖を付値環で実現し、忠実平坦な付値環拡大の一般点と閉点を取る。
規約：持ち上げる始点をあらかじめ固定しない。
使われ方：G1 の subtrusive な射の付値的な性質。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry IsLocalRing
universe u

/-- 整域間の単射の Spec は、零素点を零素点へ送る。 -/
theorem specMap_zeroPrime_of_injective {R S : Type u}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) :
    Spec.map (CommRingCat.ofHom f) (⟨⊥, inferInstance⟩ : PrimeSpectrum S) =
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot f).mp hf

/-- v 判定を満たす射は、基底の特殊化の鎖を同時に持ち上げる。 -/
theorem IsSchemeVCover.liftsSpecializations {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsSchemeVCover f) {p q : Y} (h : p ⤳ q) :
    ∃ x z : X, x ⤳ z ∧ f x = p ∧ f z = q := by
  obtain ⟨W, k, hk, hkg⟩ := exists_valuation_specialization_diagram Y h
  let w₀ : PrimeSpectrum W := ⟨⊥, inferInstance⟩
  have hkw : k w₀ = p := by
    let t₀ : PrimeSpectrum (Y.residueField p) := ⟨⊥, inferInstance⟩
    have ht : Spec.map (CommRingCat.ofHom (algebraMap W (Y.residueField p))) t₀ = w₀ :=
      specMap_zeroPrime_of_injective _ (IsFractionRing.injective W (Y.residueField p))
    calc
      k w₀ = k (Spec.map (CommRingCat.ofHom (algebraMap W (Y.residueField p))) t₀) :=
        congrArg k ht.symm
      _ = (Spec.map (CommRingCat.ofHom (algebraMap W (Y.residueField p))) ≫ k) t₀ := rfl
      _ = (Y.fromSpecResidueField p) t₀ := congrArg (fun a ↦ a t₀) hkg
      _ = p := Y.fromSpecResidueField_apply p _
  obtain ⟨Z, hZ, hvalZ, e, l, he, hl⟩ := hf (CommRingCat.of W) k
  letI : IsDomain Z := hZ
  letI : ValuationRing Z := hvalZ
  letI : Algebra W Z := e.toAlgebra
  letI : Module.FaithfullyFlat W Z := he
  letI : IsLocalHom e := inferInstanceAs (IsLocalHom (algebraMap W Z))
  let z₀ : PrimeSpectrum Z := ⟨⊥, inferInstance⟩
  have he₀ : Spec.map (CommRingCat.ofHom e) z₀ = w₀ :=
    specMap_zeroPrime_of_injective e he.injective
  have hec : Spec.map (CommRingCat.ofHom e) (closedPoint Z) = closedPoint W :=
    comap_closedPoint e
  refine ⟨l z₀, l (closedPoint Z), (specializes_closedPoint z₀).map l.continuous, ?_, ?_⟩
  · calc
      f (l z₀) = (l ≫ f) z₀ := rfl
      _ = (Spec.map (CommRingCat.ofHom e) ≫ k) z₀ := congrArg (fun a ↦ a z₀) hl
      _ = p := by change k (Spec.map (CommRingCat.ofHom e) z₀) = p; rw [he₀, hkw]
  · calc
      f (l (closedPoint Z)) = (l ≫ f) (closedPoint Z) := rfl
      _ = (Spec.map (CommRingCat.ofHom e) ≫ k) (closedPoint Z) :=
        congrArg (fun a ↦ a (closedPoint Z)) hl
      _ = q := by change k (Spec.map (CommRingCat.ofHom e) (closedPoint Z)) = q; rw [hec, hk]

end SerrePositivity.AlgebraicGeometry
