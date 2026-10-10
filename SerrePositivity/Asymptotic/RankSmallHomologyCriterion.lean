module

public import SerrePositivity.Asymptotic.SmallSupportedUniformLift

/-!
# 小さいランクの対象と小さいホモロジーの判定

通常の小さい長さの全ホモロジーをもつ支持つき自由列は、
小さいランクの支持つき自由列に同型となる。
逆向きには、共通の Koszul 長さ評価を使う。
-/

@[expose] public section

universe u

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
