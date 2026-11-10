module

public import SerrePositivity.AlgebraicGeometry.BlowupPrincipalBoundaryCover
public import SerrePositivity.AlgebraicGeometry.ProperFlatteningAffineBase
public import SerrePositivity.AlgebraicGeometry.SchemeCompositionDomination
public import SerrePositivity.AlgebraicGeometry.StrictTransformCenterGluing

/-!
概要：一般の被約 Noether 基底上の固有全射を、許容ブローアップと固有 fppf 射で細分する。
方針：一般平坦開の逆像を正則な主開にし、局所中心の貼り合わせとブローアップの合成を使う。
規約：一般平坦性を使うため基底を被約とする。指定された稠密平坦開がある場合は被約性は不要。
使われ方：BS17 Lemma 2.6 が参照する RG71, 5.2.2 の Noether 基底上の細分。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
private theorem flat_restrict_pullback_snd_of_flat
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (U : S.Opens) (hf : Flat (f ∣_ U)) :
    Flat (pullback.snd f g ∣_ g ⁻¹ᵁ U) := by
  have hpre : pullback.snd f g ⁻¹ᵁ g ⁻¹ᵁ U = pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := pullback.snd f g ⁻¹ᵁ g ⁻¹ᵁ U) le_rfl le_rfl (by rw [hpre]; simp)
  have hf' : Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using MorphismProperty.of_isPullback H hf'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- 三段の許容細分の基底射と境界開を照合する。
/--
概要：Noether 基底上の固有射が指定開上で平坦なら、一つの許容ブローアップで狭義変換を平坦化できる。
方針：境界の逆像を正則主開にする最初のブローアップ、局所中心の大域化、合成の共通細分を順に用いる。
規約：大域中心の補開集合を指定開に一致させる。
使われ方：固有全射のブローアップと proper fppf 射による細分。
-/
theorem exists_admissible_flat_strictTransformπ_of_proper
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (U : S.Opens) (hf : Flat (f ∣_ U)) :
    ∃ J : S.IdealSheafData, centerComplement J = U ∧ Flat (strictTransformπ f U J) := by
  let I := initialAdmissibleCenter U
  let p := blowupπ I
  let V := p ⁻¹ᵁ U
  let f₀ := pullback.snd f p
  have hV : Flat (f₀ ∣_ V) := flat_restrict_pullback_snd_of_flat f p U hf
  obtain ⟨𝒰, hfinite, h𝒰⟩ := exists_finite_affineOpenCover_blowup_principalBoundary I
  let : Finite 𝒰.I₀ := hfinite
  have hlocal (i : 𝒰.I₀) :
      ∃ K : (Spec (𝒰.X i)).IdealSheafData, IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ V) K ∧
        Flat (strictTransformπ (pullback.snd f₀ (𝒰.f i)) (𝒰.f i ⁻¹ᵁ V) K) := by
    obtain ⟨hR, a, ha, hboundary⟩ := h𝒰 i
    let : IsNoetherianRing (𝒰.X i) := hR
    have hb : 𝒰.f i ⁻¹ᵁ V = PrimeSpectrum.basicOpen a := by
      change 𝒰.f i ⁻¹ᵁ p ⁻¹ᵁ U = _
      rw [← initialAdmissibleCenter_complement U]
      exact hboundary
    have hflat := flat_restrict_pullback_snd_of_flat f₀ (𝒰.f i) V hV
    rw [hb] at hflat ⊢
    exact exists_admissible_flat_strictTransformπ_proper_affineBase _ a ha hflat
  choose K hK hKflat using hlocal
  obtain ⟨L, hL, hLflat⟩ :=
    exists_admissible_flat_strictTransformπ_of_affine_local f₀ V 𝒰 K hK hKflat
  obtain ⟨M, _, hM, g, hg⟩ :=
    exists_admissible_composition_domination I L U (initialAdmissibleCenter_admissible U) hL.ge
  obtain ⟨J, hJU, _, hτ⟩ := exists_admissible_family_refinement U
    (fun (_ : Unit) => M) (fun _ => hM)
  obtain ⟨τ, hτ⟩ := hτ ()
  let r := τ ≫ g
  let s := blowupπ L ≫ p
  have hrs : r ≫ s = blowupπ J := by
    rw [Category.assoc, hg, hτ]
  let : IsSchemeTheoreticallyDominant (r ⁻¹ᵁ s ⁻¹ᵁ U).ι := by
    rw [← Scheme.Hom.comp_preimage, hrs, ← hJU]
    exact blowup_centerComplement_isSchemeTheoreticallyDominant J
  have hL' : HasFlatOpenClosure f U s := (hasFlatOpenClosure_comp_iff f U p (blowupπ L)).mpr
    ((hasFlatOpenClosure_blowup_iff f₀ V L).mpr hLflat)
  have hJ := hL'.comp_of_dominant r
  rw [hrs] at hJ
  exact ⟨J, hJU, (hasFlatOpenClosure_blowup_iff f U J).mp hJ⟩

/--
概要：被約 Noether 基底上の固有全射は、許容ブローアップと固有 fppf 射で細分できる。
方針：一般平坦開上で平坦化の中心を作り、狭義変換の平坦性・固有性・全射性を使う。
規約：固有全射の始域や基底にアフィン性を課さない。
使われ方：BS17 Lemma 2.6 の Noether 基底上の細分。
-/
theorem exists_proper_fppf_blowup_refinement_of_proper_surjective
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    [_root_.AlgebraicGeometry.IsReduced S] (f : X ⟶ S) [IsProper f] [Surjective f] :
    ∃ (U : S.Opens) (J : S.IdealSheafData), Dense U.carrier ∧ centerComplement J = U ∧
      IsProper (blowupπ J) ∧ Surjective (blowupπ J) ∧ IsIso (blowupπ J ∣_ U) ∧
      ∃ (X' : Scheme.{u}) (g : X' ⟶ blowup J) (k : X' ⟶ X),
        IsProper g ∧ Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
          k ≫ f = g ≫ blowupπ J := by
  obtain ⟨U, hU, hf⟩ := exists_dense_open_flat_restrict_of_finiteType f
  obtain ⟨J, hJ, hflat⟩ := exists_admissible_flat_strictTransformπ_of_proper f U hf
  let : Flat (strictTransformπ f U J) := hflat
  exact ⟨U, J, hU, hJ, exists_proper_fppf_blowup_refinement_of_flat_strictTransform f U J hU hJ.ge⟩

end SerrePositivity.AlgebraicGeometry
