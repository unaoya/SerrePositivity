module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeStrictTransformCenterGluing
public import SerrePositivity.AlgebraicGeometry.FiniteTypeFlatteningAffineBase
public import SerrePositivity.AlgebraicGeometry.BlowupPrincipalBoundaryCover
public import SerrePositivity.AlgebraicGeometry.SchemeCompositionDomination

/-!
概要：指定した平坦開に沿って、Noether 基底上の有限型射を平坦化する。
方針：最初のブローアップで境界を局所的に正則な主開にし、局所中心を共通細分する。
規約：元の射は局所有限型かつ準コンパクト。固有性は仮定しない。
使われ方：Rydh 3.7 の Noether 模型上の指定開を保つ平坦化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_flat_restrict_pullback_snd_of_flat
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
-- 三段の許容細分の基底射と境界開を照合する。
/--
概要：Noether 基底上の有限型射が指定開上で平坦なら、一つの許容ブローアップで狭義変換を平坦化できる。
方針：境界の逆像を正則主開にする最初のブローアップ、局所中心の大域化、合成の共通細分を順に用いる。
規約：大域中心の補開集合を指定開に一致させる。
使われ方：一般の平坦開からの有限型射の平坦化。
-/
theorem exists_admissible_flat_strictTransformπ_of_finiteType
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (U : S.Opens) (hf : Flat (f ∣_ U)) :
    ∃ J : S.IdealSheafData, centerComplement J = U ∧ Flat (strictTransformπ f U J) := by
  let I := initialAdmissibleCenter U
  let p := blowupπ I
  let V := p ⁻¹ᵁ U
  let f₀ := pullback.snd f p
  have hV : Flat (f₀ ∣_ V) := finiteType_flat_restrict_pullback_snd_of_flat f p U hf
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
    have hflat := finiteType_flat_restrict_pullback_snd_of_flat f₀ (𝒰.f i) V hV
    rw [hb] at hflat ⊢
    exact exists_admissible_flat_strictTransformπ_finiteType_affineBase _ a ha hflat
  choose K hK hKflat using hlocal
  obtain ⟨L, hL, hLflat⟩ :=
    exists_admissible_flat_strictTransformπ_of_affine_local_of_finiteType f₀ V 𝒰 K hK hKflat
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
  have hL' : HasFlatOpenClosure f U s := (hasFlatOpenClosure_comp_iff_of_finiteType f U p (blowupπ L)).mpr
    ((hasFlatOpenClosure_blowup_iff f₀ V L).mpr hLflat)
  have hJ := hL'.comp_of_dominant_of_finiteType r
  rw [hrs] at hJ
  exact ⟨J, hJU, (hasFlatOpenClosure_blowup_iff f U J).mp hJ⟩

end SerrePositivity.AlgebraicGeometry
