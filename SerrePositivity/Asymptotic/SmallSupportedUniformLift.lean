module

public import SerrePositivity.Asymptotic.SupportedUniformLift
public import SerrePositivity.Asymptotic.FamilyPostnikov

/-!
# 小さいホモロジーから小さいランクの一様な代表へ

支持つき小対象の三角部分圏に Postnikov 帰納法を適用する。
長さ o(s) の heart 対象の自由分解を出発点にして、全次数のホモロジーが
小さい共通有界な導来対象の族を、小さいランクの支持つき自由列で表す。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open IsLocalRing Filter Asymptotics

variable {A : Type u} [CommRing A] {J : Ideal A} (lam : NormalizedLength A J) (s : ℕ → ℕ)

/-- 長さで制限された圏の小対象を、加群列の圏の対象の条件として読む。 -/
def smallLengthFamily : ObjectProperty (ModuleSequence A) :=
  (smallSequenceLength lam s).map (lengthBoundedSequence lam s).ι

instance : (smallLengthFamily lam s).ContainsZero := by
  unfold smallLengthFamily
  infer_instance

instance : (smallLengthFamily lam s).IsClosedUnderIsomorphisms := by
  unfold smallLengthFamily
  infer_instance

/-- 小さい加群列の条件は、一様冪ねじれ性・有限長性・通常の o(s) 条件。 -/
lemma smallLengthFamily_iff (M : ModuleSequence A) :
    smallLengthFamily lam s M ↔ lengthBoundedSequence lam s M ∧
      (fun n : ℕ ↦ (lam.len (M.obj ⟨n⟩)).toReal) =o[atTop] (fun n ↦ (s n : ℝ)) := by
  constructor
  · rintro ⟨N, hN, ⟨e⟩⟩
    have hb := (lengthBoundedSequence lam s).prop_of_iso e N.property
    exact ⟨hb, (smallSequenceLength lam s).prop_of_iso
      (ObjectProperty.isoMk _ e : N ≅ ⟨M, hb⟩) hN⟩
  · rintro ⟨hb, hs⟩
    exact ⟨⟨M, hb⟩, hs, ⟨Iso.refl M⟩⟩

variable {s} [Nontrivial A] [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)

/-- 支持つき小対象の第 n 段への三角関手。 -/
noncomputable abbrev smallSupportedDerivedEvaluation (n : ℕ) :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (rankSmallBounded.inverseImage (supportedSequence z).ι).ι ⋙ supportedDerivedEvaluation z n

noncomputable instance smallSupportedDerivedEvaluation_commShift (n : ℕ) :
    (smallSupportedDerivedEvaluation (s := s) z n).CommShift ℤ := by
  dsimp only [smallSupportedDerivedEvaluation]
  infer_instance

instance smallSupportedDerivedEvaluation_isTriangulated (n : ℕ) :
    (smallSupportedDerivedEvaluation (s := s) z n).IsTriangulated := by
  dsimp only [smallSupportedDerivedEvaluation]
  infer_instance

omit [Nontrivial A] in
/-- 支持つき小対象の射も成分ごとに同時に持ち上がる。 -/
lemma smallSupportedDerivedEvaluation_full
    (X Y : (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).FullSubcategory)
    (f : ∀ n, (smallSupportedDerivedEvaluation z n).obj X ⟶
      (smallSupportedDerivedEvaluation z n).obj Y) :
    ∃ g : X ⟶ Y, ∀ n, (smallSupportedDerivedEvaluation z n).map g = f n := by
  obtain ⟨g, hg⟩ := supportedDerivedEvaluation_full z X.obj Y.obj f
  exact ⟨⟨g⟩, hg⟩

/-- 共通有界で小さいランクの支持つき自由列によって表せる族。 -/
abbrev smallSupportedDerivedImage := familyEssImage (smallSupportedDerivedEvaluation (s := s) z)

variable [IsLocalRing A]
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))

include hK hKf hKn hKb in
omit [Nontrivial A] in
/-- 小さい長さの加群列を一つの次数に置いた族の、小さいランクでの持ち上げ。 -/
lemma smallSupportedDerivedImage_single
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s)
    (hM : smallSequenceLength _ s M) (q : ℤ) : smallSupportedDerivedImage (s := s) z
      (fun n ↦ (DerivedCategory.singleFunctor (ModuleCat A) q).obj (M.obj.obj ⟨n⟩)) := by
  obtain ⟨F, ha, hb, hres, hsupp, hsmall⟩ :=
    ordinarySmallHeart_has_supported_resolution z K hK hKf hKn d hKb M hM
  have hsF : rankSmallBounded (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) :=
    ObjectProperty.le_isoClosure _ _ ((rankSmallHomotopy_quotient F).2 hsmall)
  have hzero : smallSupportedDerivedImage (s := s) z
      (fun n ↦ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj (M.obj.obj ⟨n⟩)) :=
    ⟨⟨⟨sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩, hsupp⟩, hsF⟩, fun n ↦
      ⟨supportedDerivedEvaluation_complexIso z F _ hsupp n ≪≫
        resolutionDerivedIso _ _ (hres n).some⟩⟩
  exact familyEssImage_of_iso _ (familyEssImage_shift _ hzero (-q)) (fun n ↦
    ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (-q) q 0 (by omega)).app
      (M.obj.obj ⟨n⟩))

include hK hKf hKn hKb in
omit [Nontrivial A] in
/-- 全ホモロジーが小さい一様有界な族には、小さいランクの支持つき代表がある。 -/
theorem smallSupportedDerivedImage_of_uniform_bounds
    (X : ℕ → DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hge : ∀ n, (X n).IsGE a) (hle : ∀ n, (X n).IsLE b)
    (hH : ∀ q, smallLengthFamily (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s
      (Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat A) q).obj (X n)))) :
    smallSupportedDerivedImage (s := s) z X := by
  apply familyPostnikov_uniform _ _ (fun h e ↦ familyEssImage_of_iso _ h e)
    (familyEssImage_extension _ (smallSupportedDerivedEvaluation_full z)) ?_ X a b hge hle hH
  intro M hM q
  obtain ⟨N, hN, ⟨e⟩⟩ := hM
  exact familyEssImage_of_iso _ (smallSupportedDerivedImage_single z K hK hKf hKn d hKb N hN q)
    (fun n ↦ (DerivedCategory.singleFunctor _ q).mapIso (e.app ⟨n⟩))

end SerrePositivity.Asymptotic
