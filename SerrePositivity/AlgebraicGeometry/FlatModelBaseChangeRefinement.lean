module

public import SerrePositivity.AlgebraicGeometry.ClosedRestrictionBaseChange
public import SerrePositivity.AlgebraicGeometry.IteratedModelBaseChange
public import SerrePositivity.AlgebraicGeometry.DenseOpenModelBaseChange
public import SerrePositivity.AlgebraicGeometry.ClosedEnvelopeFlatRefinement

/-!
概要：実際の平坦化模型と tensor の pullback 比較から、元の基底の fppf–proper 細分を作る。
方針：模型の基底と閉部分を底変換し、v 判定・開の包含・稠密性を C02 へ渡す。
規約：Rydh Proposition 3.7 の既存構成の組立て。模型の存在自体は呼出側で供給する。
使われ方：非 Noether affine 基底での compact minimal primes の場合の A07。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 実際の平坦な閉部分を持つ模型を底変換し、元の v 被覆の fppf–proper 細分を作る。 -/
theorem exists_fppf_proper_refinement_of_flat_model
    {R : CommRingCat.{u}} {X X₀ S₀ Y₀ Z₀ : Scheme.{u}}
    {a : X ⟶ X₀} {x : X ⟶ Spec R} {f₀ : X₀ ⟶ S₀} {g : Spec R ⟶ S₀}
    (hX : IsPullback a x f₀ g) (hx : IsSchemeVCover x)
    (p₀ : Y₀ ⟶ S₀) [IsProper p₀] [LocallyOfFinitePresentation p₀]
    (i₀ : Z₀ ⟶ pullback f₀ p₀) [IsClosedImmersion i₀]
    [Flat (i₀ ≫ pullback.snd f₀ p₀)]
    [LocallyOfFinitePresentation (i₀ ≫ pullback.snd f₀ p₀)]
    [QuasiCompact (i₀ ≫ pullback.snd f₀ p₀)]
    (U₀ : S₀.Opens) (hP₀ : ∀ s : S₀, s ∈ U₀ → s ∈ Set.range p₀)
    (hUc : IsCompact (g ⁻¹ᵁ U₀ : Set (Spec R))) (hUd : Dense (g ⁻¹ᵁ U₀ : Set (Spec R)))
    (hI : ∀ z : (pullback f₀ p₀ : Scheme.{u}),
      pullback.snd f₀ p₀ z ∈ p₀ ⁻¹ᵁ U₀ → z ∈ Set.range i₀) :
    ∃ (T W : Scheme.{u}) (q : W ⟶ T) (r : T ⟶ Spec R) (b : W ⟶ X),
      IsProper r ∧ LocallyOfFinitePresentation r ∧ Surjective r ∧ Flat q ∧
      LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ Surjective q ∧ b ≫ x = q ≫ r := by
  classical
  let Y := pullback p₀ g
  let v : Y ⟶ Y₀ := pullback.fst p₀ g
  let p : Y ⟶ Spec R := pullback.snd p₀ g
  have hY : IsPullback v p p₀ g := IsPullback.of_hasPullback _ _
  let F := pullback.snd f₀ p₀
  let f := pullback.snd F v
  let i := closedRestrictionBaseChangeMap F i₀ v
  letI : IsClosedImmersion i := isClosedImmersion_closedRestrictionBaseChangeMap F i₀ v
  obtain ⟨hflat, hfp, hqc⟩ := closedRestrictionBaseChangeMap_properties F i₀ v
  letI : Flat (i ≫ f) := hflat
  letI : LocallyOfFinitePresentation (i ≫ f) := hfp
  letI : QuasiCompact (i ≫ f) := hqc
  have hf : IsSchemeVCover f := isSchemeVCover_iteratedModelBaseChange hX hY hx
  let U := v ⁻¹ᵁ p₀ ⁻¹ᵁ U₀
  have hpre : U = p ⁻¹ᵁ g ⁻¹ᵁ U₀ := by
    dsimp only [U]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hY.w]
  have hUcompact : IsCompact (U : Set Y) := by
    rw [hpre]
    exact p.isCompact_preimage hUc
  have hUp : DenseRange (U.ι ≫ p) := by
    have hd := denseRange_openRestriction_of_model_baseChange hY U₀ hP₀ hUd
    rw [← hpre] at hd
    exact hd
  have hU : ∀ z : (pullback F v : Scheme.{u}), f z ∈ U → z ∈ Set.range i := by
    intro z hz
    exact closedRestrictionBaseChangeMap_contains_preimage F i₀ v (p₀ ⁻¹ᵁ U₀) hI z hz
  obtain ⟨T, W, q, r, c, hr, hrfp, hrsurj, hq, hqfp, hqqc, hqsurj, hcomm⟩ :=
    exists_fppf_closedEnvelope_refinement_of_flat_closedRestriction p f hf i U hUcompact hU hUp
  refine ⟨T, W, q, r, c ≫ iteratedModelBaseChangeMap hX hY,
    hr, hrfp, hrsurj, hq, hqfp, hqqc, hqsurj, ?_⟩
  rw [Category.assoc, iteratedModelBaseChangeMap_base]
  exact hcomm

end SerrePositivity.AlgebraicGeometry
