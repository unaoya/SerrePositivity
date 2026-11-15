module

public import SerrePositivity.AlgebraicGeometry.AffineVCoverFlatModelWitness
public import SerrePositivity.AlgebraicGeometry.IntegerFlatRefinementCoefficientModel
public import SerrePositivity.AlgebraicGeometry.FinitePresentationCoefficientModel
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverFlatSurjective
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverProper
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition
public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPullback

/-!
概要：有限表示な affine v 被覆の実際の有限生成係数模型を供給する。
方針：構成した固定の平坦模型の細分を有限係数段へ移し、合成の消去で v 判定を得る。
規約：元の環の Noether 性や、模型の被覆性を追加仮定にしない。
使われ方：B03 の有限型 F_p への帰着の有限表示側の出口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u v

/-- 有限表示 affine v 被覆には、同じ v 判定を満たす実際の有限生成係数模型がある。 -/
theorem exists_affineVCover_finitePresentation_coefficient_model
    (k : Type v) (R C : Type u) [CommRing k] [IsNoetherianRing k]
    [CommRing R] [Algebra k R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C]
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R C)))) :
    ∃ B : Subalgebra k R, B.FG ∧ IsNoetherianRing B ∧
      ∃ (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra B C₀),
        Algebra.FinitePresentation B C₀ ∧
        IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap B C₀))) ∧
        Nonempty (R ⊗[B] C₀ ≃ₐ[R] C) := by
  obtain ⟨A₀, hA₀, hNA₀, C₀, _, _, hC₀, ⟨e⟩⟩ :=
    exists_finitePresentation_model_over_noetherian_coefficients k R C
  letI : IsNoetherianRing A₀ := hNA₀
  letI : Algebra.FinitePresentation A₀ C₀ := hC₀
  let f := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ C₀))
  let δ := Spec.map (CommRingCat.ofHom (algebraMap A₀ R))
  let aC := Spec.map (CommRingCat.ofHom (e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : C₀ →ₐ[A₀] R ⊗[A₀] C₀).toRingHom))
  have hcartC : IsPullback aC f f₀ δ := isPullback_affineTensorModel e
  haveI : LocallyOfFinitePresentation f₀ :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr hC₀)
  obtain ⟨A, _, _, hA, hNA, Y, Z, p, q, hp, hpfp, hq, hqfp, hqqc, hqqs,
      T, r, β, hr, hrfp, hrs, hqs, l, hl⟩ :=
    exists_flat_model_refinement_witness_vCover_affineRing R C hf
  letI : Algebra.FiniteType ℤ A := hA
  letI : LocallyOfFinitePresentation p := hpfp
  letI : Flat q := hq
  letI : LocallyOfFinitePresentation q := hqfp
  letI : QuasiCompact q := hqqc
  letI : QuasiSeparated q := hqqs
  letI : IsProper r := hr
  letI : LocallyOfFinitePresentation r := hrfp
  letI : Surjective r := hrs
  letI : Surjective (pullback.snd q β) := hqs
  let lInf := l ≫ aC
  have hlInf : lInf ≫ f₀ = pullback.snd q β ≫ r ≫ δ := by
    dsimp only [lInf]
    rw [Category.assoc, hcartC.w, ← Category.assoc l f δ, hl, Category.assoc]
  obtain ⟨B₀, hB₀, Tj, Wj, Rj, Qj, lj, w, hR, hRfp, hRs, hQ, hQfp, hQqc, hQqs,
      hQs, hlf, hlw, hcart⟩ :=
    exists_integer_flat_refinement_coefficient_model A₀ R r A p q β f₀ lInf hlInf
  letI : Algebra k B₀ := inferInstanceAs (Algebra k (B₀.restrictScalars k))
  letI : IsScalarTower k A₀ B₀ := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  letI : Algebra.FiniteType k A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  letI : Algebra.FiniteType A₀ B₀ := (Subalgebra.fg_iff_finiteType B₀).mp hB₀
  have ht : Algebra.FiniteType k B₀ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k A₀) (inferInstance : Algebra.FiniteType A₀ B₀)
  have hB : (B₀.restrictScalars k).FG :=
    (Subalgebra.fg_iff_finiteType (B₀.restrictScalars k)).mpr ht
  let Cj := B₀ ⊗[A₀] C₀
  let fj := Spec.map (CommRingCat.ofHom (algebraMap B₀ Cj))
  have hcartj := isPullback_affineTensorModel (A := A₀) (R := B₀) (S := C₀)
    (B := Cj) (AlgEquiv.refl : Cj ≃ₐ[B₀] Cj)
  let m := hcartj.lift lj (Qj ≫ Rj) hlf
  have hmf : m ≫ fj = Qj ≫ Rj := hcartj.lift_snd _ _ _
  letI : IsProper Rj := hR
  letI : Surjective Rj := hRs
  letI : Flat Qj := hQ
  letI : Surjective Qj := hQs
  have hcover : IsSchemeVCover (m ≫ fj) := by
    rw [hmf]
    exact (isSchemeVCover_of_flat_surjective Qj).comp (isSchemeVCover_of_proper_surjective Rj)
  have hfj : IsSchemeVCover fj := IsSchemeVCover.of_comp hcover
  let e' : R ⊗[B₀] Cj ≃ₐ[R] C :=
    (Algebra.TensorProduct.cancelBaseChange A₀ B₀ R R C₀).trans e
  refine ⟨B₀.restrictScalars k, hB, isNoetherianRing_of_fg hB, B₀ ⊗[A₀] C₀, ?_⟩
  dsimp only [Subalgebra.restrictScalars]
  exact ⟨inferInstance, inferInstance, inferInstance, hfj, ⟨e'⟩⟩

end SerrePositivity.AlgebraicGeometry
