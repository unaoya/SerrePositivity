module

public import SerrePositivity.LengthAlgebra.FiniteQuotientComparison
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions

/-! # 有限長さの商と大きな商の有限部分との同値

零長さの核・余核をもつ射は長さを保つ。そのため、有限長さの対象を結ぶ
分数表示の中間対象も有限長さとなり、二つの商の比較関手は完全忠実である。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

set_option backward.isDefEq.respectTransparency false

/-- 有限部分圏の包含は、零長さの核・余核をもつ射を保存し反映する。 -/
lemma finiteTorsionInclusion_isoModSerre_iff
    {M N : FiniteLengthTorsion lam} (f : M ⟶ N) :
    (zeroAdditiveLength (finiteLength lam)).isoModSerre f ↔
      (zeroAdditiveLength (torsionLength lam)).isoModSerre
        ((finiteTorsionInclusion lam).map f) := by
  have hk : lam.len (kernel f).obj =
      lam.len (kernel ((finiteTorsionInclusion lam).map f)).obj :=
    torsionLength_iso lam (PreservesKernel.iso (finiteTorsionInclusion lam) f)
  have hc : lam.len (cokernel f).obj =
      lam.len (cokernel ((finiteTorsionInclusion lam).map f)).obj :=
    torsionLength_iso lam (PreservesCokernel.iso (finiteTorsionInclusion lam) f)
  change ((lam.len (kernel f).obj).toReal = 0 ∧
      (lam.len (cokernel f).obj).toReal = 0) ↔ _
  simp only [ENNReal.toReal_eq_zero_iff, (kernel f).property.2,
    (cokernel f).property.2, or_false]
  change (_ = 0 ∧ _ = 0) ↔ (_ = 0 ∧ _ = 0)
  rw [hk, hc]
  rfl

/-- 分母の出発点の長さが有限なら、その行き先の長さも有限である。 -/
lemma finiteLength_of_isoModSerre_from_finite
    {M : FiniteLengthTorsion lam} {N : PowTorsionModule J}
    (s : (finiteTorsionInclusion lam).obj M ⟶ N)
    (hs : (zeroAdditiveLength (torsionLength lam)).isoModSerre s) :
    lam.len N.obj ≠ ⊤ := by
  have h := additiveLength_eq_of_isoModSerre (zeroAdditiveLength (torsionLength lam))
    (torsionLength lam) (torsionLength_iso lam) (torsionLength_add lam) (fun _ h ↦ h) s hs
  change lam.len M.obj = lam.len N.obj at h
  rw [← h]
  exact M.property.2

set_option backward.defeqAttrib.useBackward true in
noncomputable instance finiteQuotientInclusion_full : (finiteQuotientInclusion lam).Full := by
  let F := finiteQuotientInclusion lam
  let L₁ := finiteLengthQuotientFunctor lam
  let L₂ := lengthQuotientFunctor lam
  let e : finiteTorsionInclusion lam ⋙ L₂ ≅ L₁ ⋙ F :=
    (finiteQuotientInclusionIso lam).symm
  have : L₁.EssSurj :=
    Localization.essSurj L₁ (zeroAdditiveLength (finiteLength lam)).isoModSerre
  refine F.full_of_comp_essSurj L₁ (fun M N φ ↦ ?_)
  obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.inv.app M ≫ φ' ≫ e.hom.app N :=
    ⟨e.hom.app M ≫ φ ≫ e.inv.app N, by
      simp [dsimp% e.inv_hom_id_app_assoc, dsimp% e.inv_hom_id_app]⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction L₂
    (zeroAdditiveLength (torsionLength lam)).isoModSerre φ'
  let Z : FiniteLengthTorsion lam :=
    ⟨f.Y'.obj, f.Y'.property, finiteLength_of_isoModSerre_from_finite lam f.s f.hs⟩
  let g : (zeroAdditiveLength (finiteLength lam)).isoModSerre.LeftFraction M N :=
    { Y' := Z
      f := ObjectProperty.homMk f.f.hom
      s := ObjectProperty.homMk f.s.hom
      hs := (finiteTorsionInclusion_isoModSerre_iff lam _).mpr f.hs }
  have := Localization.inverts L₁ _ _ g.hs
  refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
  rw [← cancel_mono (F.map (L₁.map g.s)), ← Functor.map_comp,
    MorphismProperty.LeftFraction.map_comp_map_s]
  have hF {X Y : FiniteLengthTorsion lam} (q : X ⟶ Y) :
      F.map (L₁.map q) = e.inv.app X ≫
        L₂.map ((finiteTorsionInclusion lam).map q) ≫ e.hom.app Y :=
    (NatIso.naturality_1 e q).symm
  rw [hF g.f, hφ', hf, hF g.s]
  change e.inv.app M ≫ L₂.map f.f ≫ e.hom.app Z =
    (e.inv.app M ≫ f.map L₂ (Localization.inverts _ _) ≫ e.hom.app N) ≫
      e.inv.app N ≫ L₂.map f.s ≫ e.hom.app Z
  simp only [Category.assoc, e.hom_inv_id_app_assoc,
    MorphismProperty.LeftFraction.map_comp_map_s_assoc]

set_option backward.defeqAttrib.useBackward true in
instance finiteQuotientInclusion_faithful : (finiteQuotientInclusion lam).Faithful := by
  let F := finiteQuotientInclusion lam
  let L₁ := finiteLengthQuotientFunctor lam
  let L₂ := lengthQuotientFunctor lam
  let e : finiteTorsionInclusion lam ⋙ L₂ ≅ L₁ ⋙ F :=
    (finiteQuotientInclusionIso lam).symm
  refine Functor.faithful_of_comp_of_hasLeftCalculusOfFractions L₁
    (zeroAdditiveLength (finiteLength lam)).isoModSerre F (fun M N f g hfg ↦ ?_)
  have hfg' : L₂.map ((finiteTorsionInclusion lam).map f) =
      L₂.map ((finiteTorsionInclusion lam).map g) := by
    change (finiteTorsionInclusion lam ⋙ L₂).map f =
      (finiteTorsionInclusion lam ⋙ L₂).map g
    rw [← NatIso.naturality_2 e f, ← NatIso.naturality_2 e g]
    change e.hom.app M ≫ F.map (L₁.map f) ≫ e.inv.app N =
      e.hom.app M ≫ F.map (L₁.map g) ≫ e.inv.app N
    rw [hfg]
  obtain ⟨Z, s, hs, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L₂
    (zeroAdditiveLength (torsionLength lam)).isoModSerre _ _).mp hfg'
  let Z' : FiniteLengthTorsion lam :=
    ⟨Z.obj, Z.property, finiteLength_of_isoModSerre_from_finite lam s hs⟩
  let s' : N ⟶ Z' := ObjectProperty.homMk s.hom
  have hs' := (finiteTorsionInclusion_isoModSerre_iff lam s').mpr hs
  have := Localization.inverts L₁ _ _ hs'
  rw [← cancel_mono (L₁.map s'), ← L₁.map_comp, ← L₁.map_comp]
  congr 1
  exact ObjectProperty.hom_ext _ (congrArg (fun f ↦ f.hom) fac)

/-- 比較関手の本質的像は、ちょうど長さが有限な対象である。 -/
theorem finiteQuotientInclusion_essImage_iff (X : LengthQuotient lam) :
    (finiteQuotientInclusion lam).essImage X ↔ extendedQuotientLength lam X ≠ ⊤ := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    rw [← extendedQuotientLength_iso lam e, finiteQuotientInclusion_length]
    exact ENNReal.ofReal_ne_top
  · intro hX
    obtain ⟨M, rfl⟩ :=
      (Localization.Construction.objEquiv
        (zeroAdditiveLength (torsionLength lam)).isoModSerre).surjective X
    let N : FiniteLengthTorsion lam := ⟨M.obj, M.property, hX⟩
    exact ⟨(finiteLengthQuotientFunctor lam).obj N,
      ⟨(finiteQuotientInclusionIso lam).app N⟩⟩

/-- 大きな商の中で、長さが有限な対象の条件。有限生成性は要求しない。 -/
def finiteLengthPart : ObjectProperty (LengthQuotient lam) :=
  fun X ↦ extendedQuotientLength lam X ≠ ⊤

instance : (finiteLengthPart lam).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    change extendedQuotientLength lam 0 ≠ ⊤
    rw [(extendedQuotientLength_eq_zero_iff lam _).mpr (isZero_zero _)]
    exact ENNReal.zero_ne_top⟩

instance : (finiteLengthPart lam).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := ne_top_of_le_ne_top hY
    (additiveLength_le_of_mono (extendedQuotientLength lam)
      (extendedQuotientLength_add lam) (fun _ ↦ bot_le) f)

instance : (finiteLengthPart lam).IsClosedUnderQuotients where
  prop_of_epi f _ hX := ne_top_of_le_ne_top hX
    (additiveLength_le_of_epi (extendedQuotientLength lam)
      (extendedQuotientLength_add lam) (fun _ ↦ bot_le) f)

instance : (finiteLengthPart lam).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    change extendedQuotientLength lam _ ≠ ⊤
    rw [extendedQuotientLength_add lam hS]
    exact ENNReal.add_ne_top.mpr ⟨h₁, h₃⟩

instance : (finiteLengthPart lam).IsSerreClass where

/-- 大きな商の有限長さ部分。Serre 部分圏なのでアーベル圏である。 -/
abbrev FiniteLengthPart := (finiteLengthPart lam).FullSubcategory

/-- 大きな商の有限部分に制限した実数値の長さ。 -/
noncomputable def finitePartLength (X : FiniteLengthPart lam) : ℝ :=
  (extendedQuotientLength lam X.obj).toReal

lemma finitePartLength_nonneg (X : FiniteLengthPart lam) : 0 ≤ finitePartLength lam X :=
  ENNReal.toReal_nonneg

lemma finitePartLength_iso {X Y : FiniteLengthPart lam} (e : X ≅ Y) :
    finitePartLength lam X = finitePartLength lam Y :=
  congrArg ENNReal.toReal (extendedQuotientLength_iso lam ((finiteLengthPart lam).ι.mapIso e))

lemma finitePartLength_add {S : ShortComplex (FiniteLengthPart lam)} (hS : S.ShortExact) :
    finitePartLength lam S.X₂ = finitePartLength lam S.X₁ + finitePartLength lam S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have h := extendedQuotientLength_add lam (hS.map (finiteLengthPart lam).ι)
  change extendedQuotientLength lam S.X₂.obj =
    extendedQuotientLength lam S.X₁.obj + extendedQuotientLength lam S.X₃.obj at h
  dsimp only [finitePartLength]
  rw [h, ENNReal.toReal_add S.X₁.property S.X₃.property]

lemma finitePartLength_eq_zero_iff (X : FiniteLengthPart lam) :
    finitePartLength lam X = 0 ↔ IsZero X := by
  rw [finitePartLength, ENNReal.toReal_eq_zero_iff]
  have hX : extendedQuotientLength lam X.obj ≠ ⊤ := X.property
  simp only [hX, or_false]
  rw [extendedQuotientLength_eq_zero_iff]
  exact ⟨IsZero.of_full_of_faithful_of_isZero (finiteLengthPart lam).ι X,
    (finiteLengthPart lam).ι.map_isZero⟩

/-- 完全忠実な比較関手を、有限長さ部分に値をもつ関手として扱う。 -/
noncomputable def finiteQuotientToFinitePart : FiniteLengthQuotient lam ⥤ FiniteLengthPart lam :=
  (finiteLengthPart lam).lift (finiteQuotientInclusion lam) (fun X ↦ by
    change extendedQuotientLength lam ((finiteQuotientInclusion lam).obj X) ≠ ⊤
    rw [finiteQuotientInclusion_length]
    exact ENNReal.ofReal_ne_top)

instance : (finiteQuotientToFinitePart lam).Full :=
  inferInstanceAs ((finiteLengthPart lam).lift _ _).Full

instance : (finiteQuotientToFinitePart lam).Faithful :=
  inferInstanceAs ((finiteLengthPart lam).lift _ _).Faithful

instance : (finiteQuotientToFinitePart lam).EssSurj where
  mem_essImage X := by
    obtain ⟨Y, ⟨e⟩⟩ := (finiteQuotientInclusion_essImage_iff lam X.obj).mpr X.property
    exact ⟨Y, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (finiteQuotientToFinitePart lam).IsEquivalence where

/-- 有限長さの加群を先に集めた商と、大きな商の有限長さ部分との圏同値。 -/
noncomputable def finiteQuotientEquivalence : FiniteLengthQuotient lam ≌ FiniteLengthPart lam :=
  (finiteQuotientToFinitePart lam).asEquivalence

/-- 同値を大きな商への包含と合成すると、元の比較関手になる。 -/
noncomputable def finiteQuotientEquivalenceCompInclusionIso :
    (finiteQuotientEquivalence lam).functor ⋙ (finiteLengthPart lam).ι ≅
      finiteQuotientInclusion lam := Iso.refl _

/-- 同値と元の二つの商関手の可換性。 -/
noncomputable def finiteQuotientEquivalenceQuotientIso :
    finiteLengthQuotientFunctor lam ⋙
        (finiteQuotientEquivalence lam).functor ⋙ (finiteLengthPart lam).ι ≅
      finiteTorsionInclusion lam ⋙ lengthQuotientFunctor lam :=
  finiteQuotientInclusionIso lam

/-- 圏同値は拡大実数値の長さを保つ。 -/
theorem finiteQuotientEquivalence_length (X : FiniteLengthQuotient lam) :
    extendedQuotientLength lam ((finiteQuotientEquivalence lam).functor.obj X).obj =
      ENNReal.ofReal (quotientLength lam X) := finiteQuotientInclusion_length lam X

/-- 有限値を実数に移した長さも一致する。 -/
theorem finiteQuotientEquivalence_length_toReal (X : FiniteLengthQuotient lam) :
    (extendedQuotientLength lam ((finiteQuotientEquivalence lam).functor.obj X).obj).toReal =
      quotientLength lam X := by
  rw [finiteQuotientEquivalence_length, ENNReal.toReal_ofReal (quotientLength_nonneg lam X)]

/-- 逆同値による長さの一致。 -/
theorem finiteQuotientEquivalence_inverse_length (X : FiniteLengthPart lam) :
    quotientLength lam ((finiteQuotientEquivalence lam).inverse.obj X) =
      (extendedQuotientLength lam X.obj).toReal := by
  rw [← finiteQuotientEquivalence_length_toReal]
  exact congrArg ENNReal.toReal (extendedQuotientLength_iso lam
    ((finiteLengthPart lam).ι.mapIso ((finiteQuotientEquivalence lam).counitIso.app X)))

end SerrePositivity.LengthAlgebra
