module

public import SerrePositivity.Asymptotic.SupportedDerivedImage
public import SerrePositivity.Asymptotic.OrdinaryHeartResolution
public import SerrePositivity.CategoryTheory.DerivedPure

/-! # 一様な単一次数の導来対象の族を支持つき自由列で表す -/

@[expose] public section

universe u

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
