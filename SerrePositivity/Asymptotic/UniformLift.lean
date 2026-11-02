module

public import SerrePositivity.Asymptotic.SequenceComplex
public import SerrePositivity.Asymptotic.SequenceHomology
public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.CategoryTheory.TStructure.Family
public import SerrePositivity.Asymptotic.LengthSequence
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.CategoryTheory.Derived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import SerrePositivity.CategoryTheory.TStructure.Localization

/-! # 導来対象の族の一様な自由持ち上げと t 構造

## 概要

台を持つ自由列から導来対象の族への像の閉包性と、通常の長さの heart の対象の一様な自由分解を与え、共通のホモロジー次数範囲を持つ有界な導来対象の族を共通有界な台つき自由列で表す（小さいホモロジーなら小さいランクで）。小さいランクの部分圏をホモロジーの核として表し、台を持つ自由列の圏とランク商の有界 t 構造と冪等完備性を与える。

## 方針

有限 Postnikov 構成と段ごとの完全忠実性で持ち上げる。商の冪等完備性は有界 t 構造から得る。

## 規約

heart での持ち上げと、商の任意の対象の持ち上げは区別する。

## 使われ方

`Completed`、Paper/Section4。
-/

@[expose] public noncomputable section

universe u

section SupportedDerivedImagePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} R)] {e : ℕ} (z : Fin e → R)

/-- 一様に支持された自由列の第 n 段を導来圏に送る三角関手。 -/
noncomputable abbrev supportedDerivedEvaluation (n : ℕ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (supportedSequence z).ι ⋙ boundedHomotopyInclusion _ ⋙
    (FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- 各段の導来射は、支持つき自由列の一つの射として同時に持ち上がる。 -/
lemma supportedDerivedEvaluation_full
    (X Y : (supportedSequence (s := s) z).FullSubcategory)
    (f : ∀ n, (supportedDerivedEvaluation z n).obj X ⟶ (supportedDerivedEvaluation z n).obj Y) :
    ∃ g : X ⟶ Y, ∀ n, (supportedDerivedEvaluation z n).map g = f n := by
  obtain ⟨g, hg⟩ := (pointwiseDerived (R := R) (s := s)).map_surjective
    (show pointwiseDerived.obj X.obj ⟶ pointwiseDerived.obj Y.obj from f)
  exact ⟨⟨g⟩, fun n ↦ congrFun hg n⟩

/-- 各段で与えた導来同型は、元の支持つき自由列の同型に持ち上がる。 -/
noncomputable def supportedDerivedEvaluation_preimageIso
    (X Y : (supportedSequence (s := s) z).FullSubcategory)
    (i : ∀ n, (supportedDerivedEvaluation z n).obj X ≅ (supportedDerivedEvaluation z n).obj Y) :
    X ≅ Y :=
  ObjectProperty.isoMk _ ((pointwiseDerived (R := R) (s := s)).preimageIso (Pi.isoMk i))

/-- 支持つき列のホモロジーと段ごとの導来ホモロジーとの比較。 -/
noncomputable def supportedDerivedHomologyIso
    (X : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ) :
    Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj
      ((supportedDerivedEvaluation z n).obj X)) ≅ (sequenceHomology q).obj X.obj :=
  Discrete.natIso (fun n ↦ (DerivedCategory.homologyFunctorFactorsh (ModuleCat R) q).app
    (((FreeSequence.evaluation n.as).mapHomotopyCategory (.up ℤ)).obj X.obj.obj))

/-- 導来対象の族が、共通有界な支持つき自由列で表せるという条件。 -/
abbrev supportedDerivedImage := familyEssImage (supportedDerivedEvaluation (s := s) z)

/-- 支持つき自由列による代表は、成分ごとの完全三角形で拡大できる。 -/
lemma supportedDerivedImage_extension
    (T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : ∀ n, T n ∈ distTriang _)
    (h₁ : supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₁))
    (h₃ : supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₃)) :
    supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₂) :=
  familyEssImage_extension _ (supportedDerivedEvaluation_full z) T hT h₁ h₃

end SerrePositivity.Asymptotic

end SupportedDerivedImagePart

section OrdinaryHeartResolutionPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter Asymptotics
open scoped ENNReal

variable {A : Type u} [CommRing A]

/-- 指定した台のイデアル上で使う通常の長さ。値は通常の加群の長さと同じ。 -/
noncomputable def ordinaryLengthOnIdeal (J : Ideal A) : NormalizedLength A J :=
  (NormalizedLength.ordinary A).restrict J (fun M _ _ _ ↦ IsPowTorsion.bot (M := M))

@[simp] lemma ordinaryLengthOnIdeal_len (J : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] :
    (ordinaryLengthOnIdeal J).len M = (Module.length A M : ℝ≥0∞) := rfl

/-- heart の加群列の各段は有限長。 -/
lemma ordinaryLengthSequence_finite {J : Ideal A} {s : ℕ → ℕ}
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal J) s) (n : ℕ) :
    IsFiniteLength A (M.obj.obj ⟨n⟩) :=
  Module.length_ne_top_iff.mp (ENat.toENNReal_ne_top.mp (M.property.2.1 n))

/-- heart の長さの条件を、自由分解の階数評価に用いる自然数値の長さに直す。 -/
lemma ordinaryLengthSequence_isBigO {J : Ideal A} {s : ℕ → ℕ}
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal J) s) :
    (fun n : ℕ ↦ ((Module.length A (M.obj.obj ⟨n⟩)).toNat : ℝ)) =O[atTop]
      (fun n ↦ (s n : ℝ)) := by
  simpa only [ordinaryLengthOnIdeal_len, toReal_toENNReal] using M.property.2.2

variable [IsLocalRing A] {s : ℕ → ℕ} {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))

include hK hKf hKn hKb in
/-- 実際の heart の各対象に、一様に支持された共通有界自由分解を与える。 -/
theorem ordinaryHeart_has_supported_resolution
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s) :
    ∃ (F : CochainComplex (FreeSequence A s) ℤ)
      (ha : F.IsStrictlyGE (-(d : ℤ))) (hb : F.IsStrictlyLE 0),
      (∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj.obj ⟨n⟩))) ∧
      supportedSequence z (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) ∧
      ∀ i n, (F.X i).rank n =
        (Module.length A (M.obj.obj ⟨n⟩)).toNat * Module.finrank A (K.X i) := by
  obtain ⟨F, ⟨ha, hb⟩, hres, hrank⟩ := exists_sequence_resolution K hK hKf hKn d hKb
    (fun n ↦ M.obj.obj ⟨n⟩) (ordinaryLengthSequence_finite M) (ordinaryLengthSequence_isBigO M)
  obtain ⟨k, hk⟩ := M.property.1
  refine ⟨F, ha, hb, hres, ?_, hrank⟩
  apply sequence_resolution_supported z F d ha hb _ hres (k + 1) (by omega)
  intro n j
  have hz : z j ^ k ∈ Module.annihilator A (M.obj.obj ⟨n⟩) :=
    hk n (Ideal.pow_mem_pow (Ideal.subset_span (show z j ∈ Set.range z from ⟨j, rfl⟩)) k)
  ext x
  change z j ^ (k + 1) • x = 0
  rw [pow_succ', mul_smul, Module.mem_annihilator.mp hz x, smul_zero]

/-- 上の分解の第零ホモロジーは、元の加群列に同型。 -/
noncomputable def sequenceResolutionHomologyZeroIso
    (M : ModuleSequence A) (F : CochainComplex (FreeSequence A s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence A s) F)
    (hres : ∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj ⟨n⟩))) :
    (sequenceHomology 0).obj (sequenceHomotopyObj F hF) ≅ M :=
  sequenceHomologyComplexIso F hF 0 ≪≫ Discrete.natIso (fun n ↦ (hres n.as).some.homologyZeroIso)

omit [IsLocalRing A] in
/-- 分解の他の次数のホモロジーは、加群列の圏でも零。 -/
lemma sequenceResolutionHomology_isZero
    (M : ModuleSequence A) (F : CochainComplex (FreeSequence A s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence A s) F)
    (hres : ∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj ⟨n⟩)))
    (q : ℤ) (hq : q ≠ 0) : IsZero ((sequenceHomology q).obj (sequenceHomotopyObj F hF)) := by
  apply IsZero.of_iso _ (sequenceHomologyComplexIso F hF q)
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact ((hres n.as).some.isZero_homology q hq).eq_of_src _ _

include hK hKf hKn hKb in
/-- 通常の `o(s)` の heart 対象には、小さいランクで一様に支持された自由分解がある。 -/
theorem ordinarySmallHeart_has_supported_resolution
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s)
    (hM : smallSequenceLength _ s M) :
    ∃ (F : CochainComplex (FreeSequence A s) ℤ)
      (ha : F.IsStrictlyGE (-(d : ℤ))) (hb : F.IsStrictlyLE 0),
      (∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj.obj ⟨n⟩))) ∧
      supportedSequence z (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) ∧ rankSmallComplex F := by
  obtain ⟨F, ha, hb, hres, hsupp, hrank⟩ :=
    ordinaryHeart_has_supported_resolution z K hK hKf hKn d hKb M
  refine ⟨F, ha, hb, hres, hsupp, ⟨-(d : ℤ), 0, ha, hb⟩, fun i ↦ ?_⟩
  have hlen : (fun n : ℕ ↦ ((Module.length A (M.obj.obj ⟨n⟩)).toNat : ℝ)) =o[atTop]
      (fun n ↦ (s n : ℝ)) := by
    simpa only [smallSequenceLength, ordinaryLengthOnIdeal_len, toReal_toENNReal] using hM
  apply (hlen.const_mul_left (Module.finrank A (K.X i) : ℝ)).congr_left
  intro n
  rw [hrank, Nat.cast_mul, mul_comm]

end SerrePositivity.Asymptotic

end OrdinaryHeartResolutionPart

section SupportedPureDerivedImagePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing

variable {A : Type u} [CommRing A] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)

/-- 自由列の代表複体に対する導来評価の比較。 -/
noncomputable def supportedDerivedEvaluation_complexIso
    (F : CochainComplex (FreeSequence A s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence A s) F)
    (hsupp : supportedSequence z (sequenceHomotopyObj F hF)) (n : ℕ) :
    (supportedDerivedEvaluation z n).obj ⟨sequenceHomotopyObj F hF, hsupp⟩ ≅
      DerivedCategory.Q.obj ((evaluateComplex n).obj F) :=
  DerivedCategory.Qh.mapIso (((FreeSequence.evaluation n).mapHomotopyCategoryFactors (.up ℤ)).app F)
    ≪≫ (DerivedCategory.quotientCompQhIso (ModuleCat A)).app _

/-- 支持つき自由列の導来評価には共通のホモロジー次数範囲がある。 -/
lemma supportedDerivedEvaluation_uniform_bounds
    (X : (supportedSequence (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ n, ((supportedDerivedEvaluation z n).obj X).IsGE a ∧
      ((supportedDerivedEvaluation z n).obj X).IsLE b := by
  obtain ⟨⟨Y, hY⟩, hzY⟩ := X
  obtain ⟨F, rfl⟩ := Y.quotient_obj_surjective
  have hF := (boundedHomotopyProperty_quotient _ F).1 hY
  obtain ⟨a, b, ha, hb⟩ := hF
  refine ⟨a, b, fun n ↦ ?_⟩
  let i := supportedDerivedEvaluation_complexIso z F ⟨a, b, ha, hb⟩ hzY n
  have : ((evaluateComplex n).obj F).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact (FreeSequence.evaluation n).map_isZero (CochainComplex.isZero_of_isStrictlyGE F a j hj)
  have : ((evaluateComplex n).obj F).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact (FreeSequence.evaluation n).map_isZero (CochainComplex.isZero_of_isStrictlyLE F b j hj)
  have hge : (DerivedCategory.Q.obj ((evaluateComplex n).obj F)).IsGE a := by infer_instance
  have hle : (DerivedCategory.Q.obj ((evaluateComplex n).obj F)).IsLE b := by infer_instance
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso i.symm a,
    DerivedCategory.TStructure.t.isLE_of_iso i.symm b⟩

/-- 分解の導来対象は分解される加群を零次に置いた対象に同型。 -/
noncomputable def resolutionDerivedIso
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} A) (hP : IsResolutionOf P M) :
    DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj M := by
  have hge : (DerivedCategory.Q.obj P).IsGE 0 := (DerivedCategory.isGE_iff _ _).2 (by
    intro i hi
    exact (hP.isZero_homology i (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app P))
  have hle : (DerivedCategory.Q.obj P).IsLE 0 := (DerivedCategory.isLE_iff _ _).2 (by
    intro i hi
    exact (hP.isZero_homology i (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app P))
  exact derivedPureHomologyIso (DerivedCategory.Q.obj P) 0 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((DerivedCategory.homologyFunctorFactors _ 0).app P ≪≫ hP.homologyZeroIso)

variable [IsLocalRing A]
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))

include hK hKf hKn hKb in
/-- 長さで制限された加群列を任意の一つの次数に置いた族の持ち上げ。 -/
lemma supportedDerivedImage_single
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s) (q : ℤ) :
    supportedDerivedImage (s := s) z
      (fun n ↦ (DerivedCategory.singleFunctor (ModuleCat A) q).obj (M.obj.obj ⟨n⟩)) := by
  obtain ⟨F, ha, hb, hres, hsupp, _⟩ :=
    ordinaryHeart_has_supported_resolution z K hK hKf hKn d hKb M
  have hzero : supportedDerivedImage (s := s) z
      (fun n ↦ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj (M.obj.obj ⟨n⟩)) :=
    ⟨⟨sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩, hsupp⟩, fun n ↦
      ⟨supportedDerivedEvaluation_complexIso z F _ hsupp n ≪≫
        resolutionDerivedIso _ _ (hres n).some⟩⟩
  exact familyEssImage_of_iso _ (familyEssImage_shift _ hzero (-q)) (fun n ↦
    ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (-q) q 0 (by omega)).app
      (M.obj.obj ⟨n⟩))

include hK hKf hKn hKb in
/-- 単一次数に集中し、そのホモロジーが一様な長さ条件を満たす族の持ち上げ。 -/
lemma supportedDerivedImage_pure (X : ℕ → DerivedCategory (ModuleCat.{u} A)) (q : ℤ)
    (hge : ∀ n, (X n).IsGE q) (hle : ∀ n, (X n).IsLE q)
    (hH : lengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s
      (Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat A) q).obj (X n)))) :
    supportedDerivedImage (s := s) z X :=
  familyEssImage_of_iso _ (supportedDerivedImage_single z K hK hKf hKn d hKb ⟨_, hH⟩ q)
    (fun n ↦ (derivedPureHomologyIso (X n) q).symm)

end SerrePositivity.Asymptotic

end SupportedPureDerivedImagePart

section SupportedUniformLiftPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))

include hK hKf hKn hKb in
/-- 共通の有限次数幅をもつ複体の族を、支持つき自由列で表す。 -/
lemma supportedDerivedImage_finiteAmplitude (w : ℕ)
    (P : ℕ → CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ)
    (hge : ∀ n, (P n).IsStrictlyGE a) (hle : ∀ n, (P n).IsStrictlyLE (a + w))
    (hH : ∀ q, lengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s
      (familyHomology P q)) :
    supportedDerivedImage (s := s) z (fun n ↦ DerivedCategory.Q.obj (P n)) :=
  familyPostnikov_finiteAmplitude (lengthBoundedSequence _ s) _
    (fun h e ↦ familyEssImage_of_iso _ h e) (supportedDerivedImage_extension z)
    (fun M hM q ↦ supportedDerivedImage_single z K hK hKf hKn d hKb ⟨M, hM⟩ q)
    w P a hge hle hH

include hK hKf hKn hKb in
/-- 共通のホモロジー次数範囲と各次数の長さ条件から、自由列の同時の代表を得る。 -/
theorem supportedDerivedImage_of_uniform_bounds
    (X : ℕ → DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hge : ∀ n, (X n).IsGE a) (hle : ∀ n, (X n).IsLE b)
    (hH : ∀ q, lengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s
      (Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat A) q).obj (X n)))) :
    supportedDerivedImage (s := s) z X :=
  familyPostnikov_uniform (lengthBoundedSequence _ s) _
    (fun h e ↦ familyEssImage_of_iso _ h e) (supportedDerivedImage_extension z)
    (fun M hM q ↦ supportedDerivedImage_single z K hK hKf hKn d hKb ⟨M, hM⟩ q)
    X a b hge hle hH

end SerrePositivity.Asymptotic

end SupportedUniformLiftPart

section SmallSupportedUniformLiftPart

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

end SmallSupportedUniformLiftPart

section RankSmallHomologyCriterionPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing

section Forward

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

include hfg hJ hfin in
/-- 小さいランクの支持つき対象の全ホモロジーは、通常の o(s) 条件を満たす。 -/
theorem small_homology_of_rankSmallBounded
    (X : (supportedSequence (s := s) z).FullSubcategory)
    (hX : rankSmallBounded X.obj) (q : ℤ) :
    smallLengthFamily lam s ((sequenceHomology q).obj X.obj) := by
  obtain ⟨Y, hY, ⟨iY⟩⟩ := hX
  obtain ⟨P, rfl⟩ := Y.quotient_obj_surjective
  have hP := (rankSmallHomotopy_quotient P).mp hY
  let iP : sequenceHomotopyObj P hP.1 ≅ X.obj := ObjectProperty.isoMk _ iY.symm
  have hzP := (supportedSequence z).prop_of_iso iP.symm X.property
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z P hP.1).mp hzP
  have hb := complexHomologySequence_lengthBounded lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) P hP.1 (fun n j ↦ hn j n) q
  have hs := complexHomologySequence_isLittleO lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) P hP (fun n j ↦ hn j n) q
  exact (smallLengthFamily lam s).prop_of_iso
    ((sequenceHomologyComplexIso P hP.1 q).symm ≪≫ (sequenceHomology q).mapIso iP)
    ((smallLengthFamily_iff lam s _).2 ⟨hb, hs⟩)

end Forward

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))

include hK hKf hKn hKb in
/-- 全次数のホモロジーが小さい支持つき列は、小さいランクの対象である。 -/
theorem rankSmallBounded_of_small_homology
    (X : (supportedSequence (s := s) z).FullSubcategory)
    (hH : ∀ q, smallLengthFamily (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s
      ((sequenceHomology q).obj X.obj)) : rankSmallBounded X.obj := by
  obtain ⟨a, b, hb⟩ := supportedDerivedEvaluation_uniform_bounds z X
  have hi := smallSupportedDerivedImage_of_uniform_bounds z K hK hKf hKn d hKb
    (fun n ↦ (supportedDerivedEvaluation z n).obj X) a b
    (fun n ↦ (hb n).1) (fun n ↦ (hb n).2)
    (fun q ↦ (smallLengthFamily _ s).prop_of_iso (supportedDerivedHomologyIso z X q).symm (hH q))
  obtain ⟨Y, he⟩ := hi
  let i : Y.obj ≅ X := supportedDerivedEvaluation_preimageIso z _ _ (fun n ↦ (he n).some)
  exact (rankSmallBounded (R := A) (s := s)).prop_of_iso
    ((supportedSequence z).ι.mapIso i) Y.property

include hK hKf hKn hKb in
/-- 通常の長さに対する、ランクの小ささと全ホモロジーの小ささの同値。 -/
theorem rankSmallBounded_iff_small_homology
    (hfg : (Ideal.span (Set.range z)).FG)
    (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
      (ordinaryLengthOnIdeal (Ideal.span (Set.range z))).len
        ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)
    (X : (supportedSequence (s := s) z).FullSubcategory) :
    rankSmallBounded X.obj ↔
      ∀ q, smallLengthFamily (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s
        ((sequenceHomology q).obj X.obj) :=
  ⟨fun hX q ↦ small_homology_of_rankSmallBounded _ hfg z Ideal.le_radical hfin X hX q,
    rankSmallBounded_of_small_homology z K hK hKf hKn d hKb X⟩

end SerrePositivity.Asymptotic

end RankSmallHomologyCriterionPart

section SmallRankHomologicalKernelPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

/-- 通常の o(s) による Serre 商に値をもつホモロジー関手。 -/
noncomputable def supportedSequenceSmallHomology (q : ℤ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ SmallLengthSerreQuotient lam s :=
  supportedSequenceHomology lam hfg z hJ hfin q ⋙ smallLengthSerreQuotientFunctor lam s

instance supportedSequenceSmallHomology_additive (q : ℤ) :
    (supportedSequenceSmallHomology (s := s) lam hfg z hJ hfin q).Additive := by
  have : (smallLengthSerreQuotientFunctor lam s).Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp only [supportedSequenceSmallHomology]
  infer_instance

instance supportedSequenceSmallHomology_isHomological (q : ℤ) :
    (supportedSequenceSmallHomology (s := s) lam hfg z hJ hfin q).IsHomological where
  exact T hT := ((supportedSequenceHomology lam hfg z hJ hfin q).map_distinguished_exact T hT).map
    (smallLengthSerreQuotientFunctor lam s)

/-- 通常の小さい長さの商で零になる条件。 -/
lemma supportedSequenceSmallHomology_isZero_iff
    (X : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ) :
    IsZero ((supportedSequenceSmallHomology lam hfg z hJ hfin q).obj X) ↔
      smallLengthFamily lam s ((sequenceHomology q).obj X.obj) := by
  rw [show IsZero ((supportedSequenceSmallHomology lam hfg z hJ hfin q).obj X) ↔
      smallSequenceLength lam s ((supportedSequenceHomology lam hfg z hJ hfin q).obj X) from
    ObjectProperty.SerreClassLocalization.isZero_obj_iff (smallLengthSerreQuotientFunctor lam s)
      (smallSequenceLength lam s) ((supportedSequenceHomology lam hfg z hJ hfin q).obj X)]
  rw [smallLengthFamily_iff]
  exact ⟨fun h ↦ ⟨((supportedSequenceHomology lam hfg z hJ hfin q).obj X).property, h⟩,
    fun h ↦ h.2⟩

/-- 第零ホモロジーの全シフトと各次数のホモロジーとの比較。 -/
noncomputable def supportedSequenceSmallHomologyShiftIso
    (X : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ) :
    (supportedSequenceSmallHomology lam hfg z hJ hfin 0).obj (X⟦q⟧) ≅
      (supportedSequenceSmallHomology lam hfg z hJ hfin q).obj X :=
  (smallLengthSerreQuotientFunctor lam s).mapIso (ObjectProperty.isoMk _
    ((sequenceHomology 0).mapIso (((supportedSequence z).ι.commShiftIso q).app X) ≪≫
      sequenceHomologyShiftIso X.obj q))

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (zA : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
  (hfgA : (Ideal.span (Set.range zA)).FG)
  (hfinA : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
    (ordinaryLengthOnIdeal (Ideal.span (Set.range zA))).len
      ((koszulComplex (fun j ↦ zA j ^ v)).homology q) ≠ ⊤)

include hK hKf hKn hKb in
/-- 小さいランク部分圏は、通常の長さの商への第零ホモロジーの全シフトの核。 -/
theorem rankSmall_eq_homologicalKernel :
    rankSmallBounded.inverseImage (supportedSequence (s := s) zA).ι =
      (supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range zA)))
        hfgA zA Ideal.le_radical hfinA 0).homologicalKernel := by
  ext X
  rw [show (rankSmallBounded.inverseImage (supportedSequence (s := s) zA).ι) X ↔
      rankSmallBounded X.obj from Iff.rfl,
    rankSmallBounded_iff_small_homology zA K hK hKf hKn d hKb hfgA hfinA X]
  apply forall_congr'
  intro q
  exact (supportedSequenceSmallHomology_isZero_iff _ hfgA zA Ideal.le_radical hfinA X q).symm.trans
    (supportedSequenceSmallHomologyShiftIso _ hfgA zA Ideal.le_radical hfinA X q).isZero_iff.symm

end SerrePositivity.Asymptotic

end SmallRankHomologicalKernelPart

section SupportedSequenceTStructurePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
  (hfg : (Ideal.span (Set.range z)).FG)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
    (ordinaryLengthOnIdeal (Ideal.span (Set.range z))).len
      ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

omit [IsLocalRing A] in
/-- 成分ごとの導来評価は、支持つき自由列の射の等式を検出する。 -/
lemma supportedDerivedEvaluation_jointly_faithful
    {X Y : (supportedSequence (s := s) z).FullSubcategory} (f g : X ⟶ Y)
    (h : ∀ n, (supportedDerivedEvaluation z n).map f = (supportedDerivedEvaluation z n).map g) :
    f = g := by
  apply (supportedSequence z).ι.map_injective
  apply pointwiseDerived.map_injective
  exact funext h

include hK hKf hKn hKb hfg hfin in
/-- 標準切り詰め三角形の族の左端には、共通の支持つき自由代表がある。 -/
lemma supportedSequence_truncation_family
    (X : (supportedSequence (s := s) z).FullSubcategory) :
    ∃ T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} A)),
      (∀ n, T n ∈ distTriang _) ∧
      (∀ n, DerivedCategory.TStructure.t.le 0 (T n).obj₁) ∧
      (∀ n, DerivedCategory.TStructure.t.ge 1 (T n).obj₃) ∧
      (∀ n, Nonempty ((T n).obj₂ ≅ (supportedDerivedEvaluation z n).obj X)) ∧
      supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₁) := by
  obtain ⟨⟨Y, hY⟩, hzY⟩ := X
  obtain ⟨P, rfl⟩ := Y.quotient_obj_surjective
  have hP := (boundedHomotopyProperty_quotient _ P).1 hY
  let L := fun n ↦ (evaluateComplex n).obj P
  obtain ⟨a, b, hbound⟩ := evaluateComplex_uniform_bounds P hP
  have ha (n : ℕ) : (L n).IsStrictlyGE a := (hbound n).1
  have hH (q : ℤ) : lengthBoundedSequence
      (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s (familyHomology L q) := by
    exact (lengthBoundedSequence _ s).prop_of_iso (sequenceHomologyComplexIso P hP q)
      (sequenceHomology_lengthBounded _ hfg z Ideal.le_radical hfin
        (sequenceHomotopyObj P hP) hzY q)
  refine ⟨fun n ↦ DerivedCategory.triangleOfSES ((L n).shortComplexTruncLE_shortExact 0),
    fun n ↦ DerivedCategory.triangleOfSES_distinguished _, fun n ↦ ?_, fun n ↦ ?_,
    fun n ↦ ⟨(supportedDerivedEvaluation_complexIso z P hP hzY n).symm⟩, ?_⟩
  · change DerivedCategory.TStructure.t.le 0 (DerivedCategory.Q.obj ((L n).truncLE 0))
    exact DerivedCategory.TStructure.t.le_of_isLE _ 0
  · let i := asIso (DerivedCategory.Q.map ((L n).shortComplexTruncLEX₃ToTruncGE 0 1 rfl))
    exact (DerivedCategory.TStructure.t.ge 1).prop_of_iso i.symm
      (DerivedCategory.TStructure.t.ge_of_isGE _ 1)
  · apply supportedDerivedImage_of_uniform_bounds z K hK hKf hKn d hKb
      (fun n ↦ DerivedCategory.Q.obj ((L n).truncLE 0)) a 0
      (fun n ↦ inferInstance) (fun n ↦ inferInstance)
    intro q
    exact (lengthBoundedSequence _ s).prop_of_iso
      (familyDerivedHomologyIso (fun n ↦ (L n).truncLE 0) q).symm
      (familyHomology_truncLE_prop L _ hH 0 q)

/-- 支持つき自由列上の、成分ごとのホモロジーで定まる t 構造。 -/
noncomputable def supportedSequenceTStructure :
    TStructure (supportedSequence (s := s) z).FullSubcategory :=
  familyTStructure (supportedDerivedEvaluation z) DerivedCategory.TStructure.t
    (supportedDerivedEvaluation_full z) (supportedDerivedEvaluation_jointly_faithful z)
    (supportedSequence_truncation_family z K hK hKf hKn d hKb hfg hfin)

/-- 各段の導来評価は t 完全である。 -/
lemma supportedSequenceTStructure_evaluation_tExact (n : ℕ) :
    (supportedDerivedEvaluation (s := s) z n).TExact
      (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin) DerivedCategory.TStructure.t :=
  familyTStructure_tExact _ _ _ _ _ n

/-- 共通の次数範囲により、この t 構造は有界である。 -/
lemma supportedSequenceTStructure_bounded
    (X : (supportedSequence (s := s) z).FullSubcategory) :
    (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).bounded X := by
  obtain ⟨a, b, hb⟩ := supportedDerivedEvaluation_uniform_bounds z X
  exact ⟨⟨a, ⟨fun n ↦ (hb n).1.ge⟩⟩, ⟨b, ⟨fun n ↦ (hb n).2.le⟩⟩⟩

end SerrePositivity.Asymptotic

end SupportedSequenceTStructurePart

section SupportedRankTStructurePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
  (hfg : (Ideal.span (Set.range z)).FG)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
    (ordinaryLengthOnIdeal (Ideal.span (Set.range z))).len
      ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

omit [IsLocalRing A] in
/-- 各段のホモロジーが零なら、長さの商へのホモロジーも零。 -/
lemma supportedSequenceSmallHomology_isZero_of_derived
    (X : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ)
    (hz : ∀ n, IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) q).obj
      ((supportedDerivedEvaluation z n).obj X))) :
    IsZero ((supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range z)))
      hfg z Ideal.le_radical hfin q).obj X) := by
  apply (supportedSequenceSmallHomology_isZero_iff _ hfg z Ideal.le_radical hfin X q).2
  apply (smallLengthFamily _ s).prop_of_isZero
  apply IsZero.of_iso ?_ (supportedDerivedHomologyIso z X q).symm
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact (hz n.as).eq_of_src _ _

/-- 非正側から一段離れた対象の第零ホモロジーは消える。 -/
lemma supportedSmallHomology_zero_of_isLE
    (X : (supportedSequence (s := s) z).FullSubcategory)
    (hX : (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).IsLE X (-1)) :
    IsZero ((supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range z)))
      hfg z Ideal.le_radical hfin 0).obj X) := by
  apply supportedSequenceSmallHomology_isZero_of_derived z hfg hfin X 0
  intro n
  have : ((supportedDerivedEvaluation z n).obj X).IsLE (-1) := ⟨hX.le n⟩
  exact DerivedCategory.isZero_of_isLE _ (-1) 0 (by omega)

/-- 正の側の対象の第零ホモロジーは消える。 -/
lemma supportedSmallHomology_zero_of_isGE
    (X : (supportedSequence (s := s) z).FullSubcategory)
    (hX : (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).IsGE X 1) :
    IsZero ((supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range z)))
      hfg z Ideal.le_radical hfin 0).obj X) := by
  apply supportedSequenceSmallHomology_isZero_of_derived z hfg hfin X 0
  intro n
  have : ((supportedDerivedEvaluation z n).obj X).IsGE 1 := ⟨hX.ge n⟩
  exact DerivedCategory.isZero_of_isGE _ 1 0 (by omega)

/-- 支持つきランク商の分母は、構成した t 構造の非正切り詰めで保たれる。 -/
theorem supportedRank_truncLE_denominator
    {X Y : (supportedSequence (s := s) z).FullSubcategory} (f : X ⟶ Y)
    (hf : (rankSmallBounded.inverseImage (supportedSequence z).ι).trW f) :
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW
      (((supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).truncLE 0).map f) := by
  rw [rankSmall_eq_homologicalKernel z K hK hKf hKn d hKb hfg hfin] at hf ⊢
  exact homologicalKernel_truncLE _ _
    (supportedSmallHomology_zero_of_isLE z K hK hKf hKn d hKb hfg hfin)
    (supportedSmallHomology_zero_of_isGE z K hK hKf hKn d hKb hfg hfin) f hf

/-- 支持つき自由列のランク商上の有界 t 構造。 -/
noncomputable def supportedRankTStructure :
    TStructure (SupportedSequenceRankQuotient (s := s) z) :=
  verdierTStructure (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin)
    (rankSmallBounded.inverseImage (supportedSequence z).ι)
    (fun _ _ f hf ↦ supportedRank_truncLE_denominator z K hK hKf hKn d hKb hfg hfin f hf)

/-- 商の t 構造の有界性。 -/
lemma supportedRankTStructure_bounded (Y : SupportedSequenceRankQuotient (s := s) z) :
    (supportedRankTStructure z K hK hKf hKn d hKb hfg hfin).bounded Y :=
  verdierTStructure_bounded _ _ _
    (supportedSequenceTStructure_bounded z K hK hKf hKn d hKb hfg hfin) Y

include hK hKf hKn hKb hfg hfin in
/-- 支持つきランク商は、既に冪等完備である。 -/
theorem supportedRank_isIdempotentComplete :
    IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z) :=
  verdier_isIdempotentComplete _ _
    (fun _ _ f hf ↦ supportedRank_truncLE_denominator z K hK hKf hKn d hKb hfg hfin f hf)
    (supportedSequenceTStructure_bounded z K hK hKf hKn d hKb hfg hfin)

include hK hKf hKn hKb hfg hfin in
/-- 支持つきランク商の冪等完備化の対象は、商の前の支持つき自由列で表せる。 -/
theorem supportedRankKaroubi_has_representative
    (Y : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    ∃ X : (supportedSequence (s := s) z).FullSubcategory,
      Nonempty ((toKaroubi _).obj
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj X) ≅ Y) :=
  verdierKaroubi_has_representative _ _
    (fun _ _ f hf ↦ supportedRank_truncLE_denominator z K hK hKf hKn d hKb hfg hfin f hf)
    (supportedSequenceTStructure_bounded z K hK hKf hKn d hKb hfg hfin) Y

end SerrePositivity.Asymptotic

end SupportedRankTStructurePart
