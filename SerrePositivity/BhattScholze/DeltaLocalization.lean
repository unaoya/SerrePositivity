module

public import SerrePositivity.BhattScholze.WittTwoUnits
public import SerrePositivity.BhattScholze.DeltaSectionNaturality
public import Mathlib.RingTheory.Localization.Basic

/-! # Frobenius安定な乗法集合におけるδ局所化

BS著者公開版Lemma 2.15。W₂切断と二成分の単元判定で、pねじれのある環も
直接扱う。基底のp正則性を追加せず、Mathlibの局所化の普遍性を再利用する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable (D : DeltaStructure p R) (M : Submonoid R)
variable (B : Type v) [CommRing B] [Algebra R B] [IsLocalization M B]
variable (hφ : ∀ s : M, D.frobeniusLift s ∈ M)
include hφ

/-- 局所化先に移したW₂切断は、分母を単元に送る。 -/
theorem localization_section_isUnit (s : M) :
    IsUnit (((wittTwoMap (p := p) (algebraMap R B)).comp D.sectionHom) s) := by
  apply (wittTwo_isUnit_iff _).mpr
  constructor
  · simpa only [RingHom.comp_apply, wittTwoMap_coeff, D.coeff_zero] using
      IsLocalization.map_units B s
  · have h := IsLocalization.map_units B ⟨D.frobeniusLift s, hφ s⟩
    convert h using 1
    simp only [RingHom.comp_apply, wittTwoFrobenius_apply, wittTwoMap_coeff,
      D.coeff_zero, frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
    rfl

/-- Frobenius安定な集合における局所化のW₂切断。 -/
def localizationSection : B →+* WittTwo p B :=
  IsLocalization.lift (M := M) (S := B) (D.localization_section_isUnit M B hφ)

/-- 局所化切断は基底上で元の切断と両立する。 -/
theorem localizationSection_comp :
    (D.localizationSection M B hφ).comp (algebraMap R B) =
      (wittTwoMap (p := p) (algebraMap R B)).comp D.sectionHom :=
  IsLocalization.lift_comp _

/-- 切断と第0座標射の合成は恒等射。局所化の射の外延性から従う。 -/
theorem localizationSection_projection :
    (wittTwoProjection p B).comp (D.localizationSection M B hφ) = RingHom.id B := by
  apply IsLocalization.ringHom_ext M
  ext r
  change wittTwoProjection p B (D.localizationSection M B hφ (algebraMap R B r)) =
    algebraMap R B r
  rw [show D.localizationSection M B hφ (algebraMap R B r) =
    wittTwoMap (algebraMap R B) (D.sectionHom r) from
    DFunLike.congr_fun (D.localizationSection_comp M B hφ) r]
  simp [D.coeff_zero]

/-- Frobenius安定な分母集合による局所化のδ構造。 -/
def localization : DeltaStructure p B where
  sectionHom := D.localizationSection M B hφ
  coeff_zero := by
    intro x
    exact DFunLike.congr_fun (D.localizationSection_projection M B hφ) x

/-- 標準局所化射はδ射。 -/
theorem isDeltaHom_localization : D.IsDeltaHom (D.localization M B hφ) (algebraMap R B) := by
  apply (D.isDeltaHom_iff_sectionHom_comp _ _).mpr
  exact (D.localizationSection_comp M B hφ).symm

/-- 標準射と両立する局所化のδ構造は一意。p正則性は不要。 -/
theorem localization_unique (E : DeltaStructure p B)
    (hE : D.IsDeltaHom E (algebraMap R B)) : E = D.localization M B hφ := by
  have he := (D.isDeltaHom_iff_sectionHom_comp E _).mp hE
  have hs : E.sectionHom = (D.localization M B hφ).sectionHom := by
    apply IsLocalization.ringHom_ext M
    exact he.symm.trans (D.localizationSection_comp M B hφ).symm
  apply ext
  intro x
  exact congrArg (fun y : WittTwo p B ↦ y.coeff 1) (DFunLike.congr_fun hs x)

/-- Frobenius安定な集合での局所化は一意な適合δ構造を持つ。 -/
theorem existsUnique_localization :
    ∃! E : DeltaStructure p B, D.IsDeltaHom E (algebraMap R B) :=
  ⟨D.localization M B hφ, D.isDeltaHom_localization M B hφ,
    fun E hE ↦ D.localization_unique M B hφ E hE⟩

/-- Mの元を単元に送るδ射は、局所化から一意なδ射へ延長する。 -/
theorem existsUnique_localization_lift {A : Type w} [CommRing A]
    (E : DeltaStructure p A) (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hM : ∀ s : M, IsUnit (f s)) :
    ∃! g : B →+* A,
      g.comp (algebraMap R B) = f ∧ (D.localization M B hφ).IsDeltaHom E g := by
  let g : B →+* A := IsLocalization.lift hM
  have hg : g.comp (algebraMap R B) = f := IsLocalization.lift_comp hM
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · apply ((D.localization M B hφ).isDeltaHom_iff_sectionHom_comp E g).mpr
    apply IsLocalization.ringHom_ext M
    ext r i
    have hj := DFunLike.congr_fun (D.localizationSection_comp M B hφ) r
    have hk := (D.isDeltaHom_iff_sectionHom_comp E f).mp hf
    have hl := DFunLike.congr_fun hk r
    simp only [RingHom.comp_apply] at hj hl ⊢
    change (wittTwoMap g (D.localizationSection M B hφ (algebraMap R B r))).coeff i =
      (E.sectionHom (g (algebraMap R B r))).coeff i
    rw [hj, wittTwoMap_coeff, wittTwoMap_coeff]
    have hc (x : R) : g (algebraMap R B x) = f x := DFunLike.congr_fun hg x
    rw [hc, hc]
    simpa only [wittTwoMap_coeff] using
      congrArg (fun x : WittTwo p A ↦ x.coeff i) hl
  · intro k hk
    apply IsLocalization.ringHom_ext M
    exact hk.1.trans hg.symm

end SerrePositivity.BhattScholze.DeltaStructure
