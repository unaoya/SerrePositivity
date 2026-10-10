module

public import SerrePositivity.Asymptotic.RankSmallHomologyCriterion
public import SerrePositivity.Asymptotic.RankHomologyShift

/-! # 小さいランク部分圏を通常の小さい長さのホモロジーの核として表す -/

@[expose] public section

universe u

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
