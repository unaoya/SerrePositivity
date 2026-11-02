module

public import SerrePositivity.Asymptotic.SequenceComplex
public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.Asymptotic.Karoubi
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated

/-! # 台を持つランク商の係数変更

## 概要

行列の係数変更がスカラー倍を環準同型に沿って移すので一様な台を保つことを示し、係数変更を台を持つ部分圏に制限して小さいランクの Verdier 商に降ろす（商の前後の自然同型とシフト・完全三角形との両立つき）。二段の係数変更と直接の係数変更も比べる。

## 方針

列全体を消す共通の冪と零ホモトピーを係数変更の後も使う。

## 規約

係数変更と導来テンソル積の比較は `SequenceComplex` のもの。

## 使われ方

`Euler`・`Completed`、Paper/Section4。
-/

@[expose] public noncomputable section

universe u

section SequenceBaseChangeSupportPart

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] {s : ℕ → ℕ}

/-- 一様に台をもつ自由複体列の各段は、有限版3.5で用いる台つき完全複体である。 -/
lemma evaluateComplex_isPerfectSupported {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : scalarSupported z (sequenceHomotopyObj K hK)) (n : ℕ) :
    IsPerfectSupported z ((evaluateComplex n).obj K) := by
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK).mp hzK
  obtain ⟨a, b, ha, hb⟩ := hK
  refine ⟨⟨a, b, fun i hi ↦ ?_⟩, fun i ↦ ?_, fun i ↦ ?_, ⟨v, fun j ↦ hn j n⟩⟩
  · apply (FreeSequence.evaluation n).map_isZero
    rcases hi with hi | hi
    · exact K.isZero_of_isStrictlyGE a i hi
    · exact K.isZero_of_isStrictlyLE b i hi
  · exact inferInstanceAs (Module.Free R (Fin ((K.X i).rank n) → R))
  · exact inferInstanceAs (Module.Finite R (Fin ((K.X i).rank n) → R))

/-- 行列の係数変更は環準同型に沿ってスカラー倍を保つ。 -/
lemma FreeSequence.changeMatrix_smul (φ : R →+* S) {a b : ℕ}
    (r : R) (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    FreeSequence.changeMatrix φ (r • f) = φ r • FreeSequence.changeMatrix φ f := by
  apply Matrix.toLin'.symm.injective
  simp only [FreeSequence.changeMatrix, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_smul]
  ext i j
  simp [Matrix.map_apply, smul_eq_mul, map_mul]

/-- 複体列の係数変更の射への作用もスカラー倍と両立する。 -/
lemma changeRing_complex_map_smul (φ : R →+* S)
    {K L : CochainComplex (FreeSequence R s) ℤ} (r : R) (f : K ⟶ L) :
    ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).map (r • f) =
      φ r • ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  funext n
  exact FreeSequence.changeMatrix_smul φ r (f.f q n)

/-- 共通有界性は係数変更後にも保たれる。 -/
lemma changeRing_strictlyBounded (φ : R →+* S)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K) :
    strictlyBoundedComplex (FreeSequence S s)
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  exact ⟨a, b, inferInstance, inferInstance⟩

/-- 共通の冪による台は、自由複体列の係数変更で保たれる。 -/
lemma changeRing_complex_supported (φ : R →+* S) {ι : Type*} (z : ι → R)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : scalarSupported z (sequenceHomotopyObj K hK)) :
    scalarSupported (φ ∘ z)
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)) := by
  obtain ⟨v, hv, hzero⟩ := hzK
  refine ⟨v, hv, fun j ↦ ?_⟩
  have hq : (HomotopyCategory.quotient _ _).map (z j ^ v • 𝟙 K) = 0 := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    exact congrArg (fun f ↦ f.hom) (hzero j)
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).mp hq
  have hm := (FreeSequence.changeRing φ).mapHomotopy H
  rw [changeRing_complex_map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at hm
  have hh := (HomotopyCategory.quotient_map_eq_zero_iff _).mpr ⟨hm⟩
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, map_pow] at hh
  exact ObjectProperty.hom_ext _ hh

end SerrePositivity.Asymptotic

end SequenceBaseChangeSupportPart

section SupportedRankBaseChangePart

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] {s : ℕ → ℕ}
  (φ : R →+* S) {e : ℕ} (z : Fin e → R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 共通有界ホモトピー圏の支持条件は係数変更で保たれる。 -/
lemma changeRing_supportedSequence (X : SequenceHomotopy R s) (hX : supportedSequence z X) :
    supportedSequence (φ ∘ z) ((mapBoundedHomotopy (FreeSequence.changeRing φ)).obj X) := by
  obtain ⟨Y, hY⟩ := X
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  exact changeRing_complex_supported φ z K ((boundedHomotopyProperty_quotient _ K).mp hY) hX

/-- 一様に台をもつ自由列のホモトピー圏の係数変更関手。 -/
@[implicit_reducible]
noncomputable def supportedSequenceChangeRing :
    (supportedSequence (s := s) z).FullSubcategory ⥤
      (supportedSequence (s := s) (φ ∘ z)).FullSubcategory :=
  (supportedSequence (φ ∘ z)).lift
    ((supportedSequence z).ι ⋙ mapBoundedHomotopy (FreeSequence.changeRing φ))
    (fun X ↦ changeRing_supportedSequence φ z X.obj X.property)

noncomputable instance supportedSequenceChangeRing_commShift :
    (supportedSequenceChangeRing (s := s) φ z).CommShift ℤ := by
  dsimp only [supportedSequenceChangeRing]
  infer_instance

instance supportedSequenceChangeRing_isTriangulated :
    (supportedSequenceChangeRing (s := s) φ z).IsTriangulated := by
  dsimp only [supportedSequenceChangeRing]
  infer_instance

variable [Nontrivial R] [Nontrivial S]

omit [Nontrivial R] [Nontrivial S] in
/-- 支持つき商への係数変更は、支持つき小対象を錐とする分母を可逆にする。 -/
lemma supportedSequenceChangeRing_inverts :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.IsInvertedBy
      (supportedSequenceChangeRing φ z ⋙
        (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q) := by
  let F := supportedSequenceChangeRing (s := s) φ z
  let P := rankSmallBounded.inverseImage (supportedSequence (s := s) (φ ∘ z)).ι
  have h : rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι ≤ P.inverseImage F :=
    fun X hX ↦ changeRing_rankSmallBounded φ X.obj hX
  intro X Y f hf
  exact P.inverseImage_trW_isInverted F P.trW.Q f
    (ObjectProperty.trW_monotone h f hf)

/-- 支持部分圏のランク商に誘導される係数変更関手。 -/
@[implicit_reducible]
noncomputable def supportedRankChangeRing :
    SupportedSequenceRankQuotient (s := s) z ⥤
      SupportedSequenceRankQuotient (s := s) (φ ∘ z) :=
  Localization.lift
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedSequenceChangeRing_inverts φ z)
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q

/-- 商の前後での支持つき係数変更を比較する自然同型。 -/
noncomputable def supportedRankChangeRingFactors :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q ⋙
      supportedRankChangeRing φ z ≅
    supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q :=
  Localization.fac _ (supportedSequenceChangeRing_inverts φ z) _

noncomputable instance supportedRankChangeRing_lifting : Localization.Lifting
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedRankChangeRing φ z) := ⟨supportedRankChangeRingFactors φ z⟩

noncomputable instance supportedRankChangeRing_commShift :
    (supportedRankChangeRing (s := s) φ z).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW ℤ
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedRankChangeRing φ z)

instance supportedRankChangeRingFactors_commShift :
    NatTrans.CommShift (supportedRankChangeRingFactors (s := s) φ z).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW ℤ
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedRankChangeRing φ z)

/-- 支持つきランク商の係数変更は三角関手である。 -/
instance supportedRankChangeRing_isTriangulated :
    (supportedRankChangeRing (s := s) φ z).IsTriangulated := by
  let := Localization.essSurj_mapArrow
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
  exact Functor.isTriangulated_of_precomp_iso (supportedRankChangeRingFactors φ z)

end SerrePositivity.Asymptotic

end SupportedRankBaseChangePart

section BaseChangeCompositionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {s : ℕ → ℕ}
  (φ : R →+* S) (ψ : S →+* T)

lemma FreeSequence.changeMatrix_changeMatrix {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    changeMatrix ψ (changeMatrix φ f) = changeMatrix (ψ.comp φ) f := by
  simp only [changeMatrix, LinearMap.toMatrix'_toLin']
  rfl

noncomputable def FreeSequence.changeRingCompIso :
    changeRing (s := s) φ ⋙ changeRing ψ ≅ changeRing (ψ.comp φ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp only [Category.comp_id, Category.id_comp, Iso.refl_hom]
    funext n
    exact changeMatrix_changeMatrix φ ψ (f n))

noncomputable def sequenceChangeRingCompIso :
    mapBoundedHomotopy (FreeSequence.changeRing (s := s) φ) ⋙
      mapBoundedHomotopy (FreeSequence.changeRing ψ) ≅
        mapBoundedHomotopy (FreeSequence.changeRing (ψ.comp φ)) :=
  ((boundedHomotopyProperty (FreeSequence T s)).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (boundedHomotopyInclusion _) (Functor.mapHomotopyCategoryCompIso
      (FreeSequence.changeRingCompIso (s := s) φ ψ) (.up ℤ)))

variable {e : ℕ} (z : Fin e → R)

noncomputable def supportedSequenceChangeRingCompIso :
    supportedSequenceChangeRing (s := s) φ z ⋙ supportedSequenceChangeRing ψ (φ ∘ z) ≅
      supportedSequenceChangeRing (ψ.comp φ) z :=
  ((supportedSequence (s := s) ((ψ.comp φ) ∘ z)).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (supportedSequence z).ι (sequenceChangeRingCompIso φ ψ))

variable [Nontrivial R] [Nontrivial S] [Nontrivial T]

/-- 二段階の支持つき Verdier 商の係数変更は直接の係数変更に自然同型。 -/
noncomputable def supportedRankChangeRingCompIso :
    supportedRankChangeRing (s := s) φ z ⋙ supportedRankChangeRing ψ (φ ∘ z) ≅
      supportedRankChangeRing (ψ.comp φ) z := by
  let Q := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let Q' := (rankSmallBounded.inverseImage
    (supportedSequence (s := s) ((ψ.comp φ) ∘ z)).ι).trW.Q
  let i : Q ⋙ supportedRankChangeRing φ z ⋙ supportedRankChangeRing ψ (φ ∘ z) ≅
      Q ⋙ supportedRankChangeRing (ψ.comp φ) z :=
    isoWhiskerRight (supportedRankChangeRingFactors φ z) (supportedRankChangeRing ψ (φ ∘ z)) ≪≫
    isoWhiskerLeft (supportedSequenceChangeRing φ z) (supportedRankChangeRingFactors ψ (φ ∘ z)) ≪≫
    isoWhiskerRight (supportedSequenceChangeRingCompIso φ ψ z) Q' ≪≫
    (supportedRankChangeRingFactors (ψ.comp φ) z).symm
  exact (Localization.fullyFaithfulWhiskeringLeft Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW _).preimageIso i

/-- 冪等完備化後も二段階と直接の係数変更は一致する。 -/
noncomputable def completedSupportedChangeRingCompIso :
    (functorExtension₂ _ _).obj (supportedRankChangeRing (s := s) φ z) ⋙
      (functorExtension₂ _ _).obj (supportedRankChangeRing ψ (φ ∘ z)) ≅
        (functorExtension₂ _ _).obj (supportedRankChangeRing (ψ.comp φ) z) := by
  let F := supportedRankChangeRing (s := s) φ z
  let G := supportedRankChangeRing (s := s) ψ (φ ∘ z)
  let H := supportedRankChangeRing (s := s) (ψ.comp φ) z
  let F' := (functorExtension₂ _ _).obj F
  let G' := (functorExtension₂ _ _).obj G
  let H' := (functorExtension₂ _ _).obj H
  let i : toKaroubi _ ⋙ F' ⋙ G' ≅ toKaroubi _ ⋙ H' :=
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F) G' ≪≫
    isoWhiskerLeft F ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G) ≪≫
    isoWhiskerRight (supportedRankChangeRingCompIso φ ψ z) (toKaroubi _) ≪≫
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app H).symm
  exact ((whiskeringLeft _ _ _).obj (toKaroubi _)).preimageIso i

end SerrePositivity.Asymptotic

end BaseChangeCompositionPart
