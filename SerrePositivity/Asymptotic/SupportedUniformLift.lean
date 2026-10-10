module

public import SerrePositivity.Asymptotic.SupportedPureDerivedImage
public import SerrePositivity.Asymptotic.FamilyPostnikov

/-!
# 有界な導来対象の族の一様自由持ち上げ

共通のホモロジー次数範囲があり、各次数のホモロジー列が一様な冪で消え、
有限長かつ長さ O(s) なら、族全体を共通有界な支持つき自由列で表せる。
商や Karoubi 包絡はまだ用いず、有限 Postnikov 構成と段ごとの完全忠実性を使う。
-/

@[expose] public section

universe u

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
