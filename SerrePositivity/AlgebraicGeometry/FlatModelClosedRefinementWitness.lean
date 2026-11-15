module

public import SerrePositivity.AlgebraicGeometry.ClosedRestrictionBaseChange
public import SerrePositivity.AlgebraicGeometry.IteratedModelBaseChange
public import SerrePositivity.AlgebraicGeometry.DenseOpenModelBaseChange
public import SerrePositivity.AlgebraicGeometry.ClosedEnvelopeRefinementWitness

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
/-- 平坦な模型の細分で、実際の有限型閉イデアルと全射性・元の射への因子化を保持する。 -/
theorem exists_flat_model_closed_refinement_witness
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
    ∃ J : (pullback p₀ g).IdealSheafData, IsFiniteTypeIdealSheaf J ∧
      Surjective (J.subschemeι ≫ pullback.snd p₀ g) ∧
      Surjective (pullback.snd (pullback.snd (i₀ ≫ pullback.snd f₀ p₀)
        (pullback.fst p₀ g)) J.subschemeι) ∧
      ∃ b : pullback (pullback.snd (i₀ ≫ pullback.snd f₀ p₀)
          (pullback.fst p₀ g)) J.subschemeι ⟶ X,
        b ≫ x = pullback.snd _ _ ≫ J.subschemeι ≫ pullback.snd p₀ g := by
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
  obtain ⟨J, hJ, hr, hq⟩ :=
    exists_closedEnvelope_refinement_witness_of_flat_closedRestriction p f hf i U
      hUcompact hU hUp
  have hi : i ≫ f = pullback.snd (i₀ ≫ F) v :=
    closedRestrictionBaseChangeMap_snd F i₀ v
  rw [hi] at hq
  refine ⟨J, hJ, hr, hq,
    pullback.fst (pullback.snd (i₀ ≫ F) v) J.subschemeι ≫
      i ≫ iteratedModelBaseChangeMap hX hY, ?_⟩
  calc
    _ = pullback.fst (pullback.snd (i₀ ≫ F) v) J.subschemeι ≫ (i ≫ f) ≫ p := by
      rw [Category.assoc, Category.assoc, iteratedModelBaseChangeMap_base]
      simp only [f, F, Category.assoc]
    _ = pullback.fst (pullback.snd (i₀ ≫ F) v) J.subschemeι ≫
        pullback.snd (i₀ ≫ F) v ≫ p := by rw [hi]
    _ = _ := by rw [← Category.assoc, pullback.condition, Category.assoc]

end SerrePositivity.AlgebraicGeometry
