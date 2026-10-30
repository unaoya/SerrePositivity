module

public import SerrePositivity.Asymptotic.SequenceHomologyLocalization
public import SerrePositivity.Asymptotic.SupportedKaroubi
public import SerrePositivity.CategoryTheory.Karoubi.Basic

/-!
# 冪等完備化した支持つきランク商上のホモロジー評価

値域の長さの商はアーベル圏なので冪等完備である。その普遍性によりホモロジー関手を
形式的な直和因子に延長し、支持部分圏との圏同値を通じて全支持対象を評価する。
各対象についてホモロジーの非零次数が有限範囲に入ることも証明する。
Karoubi 包絡の三角構造との両立は、この加法的な延長とは別の課題である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界な自由列のホモロジー列は共通の有限範囲の外で零となる。 -/
lemma sequenceHomology_bounded (P : SequenceHomotopy R s) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) → IsZero ((sequenceHomology q).obj P) := by
  obtain ⟨Y, hY⟩ := P
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  have hb := (boundedHomotopyProperty_quotient _ K).mp hY
  obtain ⟨a, b, ha, hb'⟩ := hb
  have hb : strictlyBoundedComplex (FreeSequence R s) K := ⟨a, b, ha, hb'⟩
  refine ⟨a, b, fun q hq ↦ ?_⟩
  have hz : IsZero (complexHomologySequence K q) := by
    apply Functor.isZero
    intro n
    apply isZero_homology_of_isZero_X
    apply (FreeSequence.evaluation n.as).map_isZero
    rcases hq with hq | hq
    · exact CochainComplex.isZero_of_isStrictlyGE K a q hq
    · exact CochainComplex.isZero_of_isStrictlyLE K b q hq
  exact hz.of_iso (sequenceHomologyComplexIso K hb q)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 長さの商に移した後も、ホモロジーの消滅範囲は維持される。 -/
lemma supportedSequenceQuotientHomology_bounded
    (P : (supportedSequence (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  obtain ⟨a, b, hab⟩ := sequenceHomology_bounded P.obj
  refine ⟨a, b, fun q hq ↦ ?_⟩
  apply (lengthSerreQuotientFunctor lam s U hU hs).map_isZero
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact (hab q hq).eq_of_src _ _

variable [Nontrivial R]

/-- Verdier 商の全対象について、ホモロジーの非零次数は有限範囲に入る。 -/
lemma supportedRankHomology_bounded (P : SupportedSequenceRankQuotient (s := s) z) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  let L := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let := Localization.essSurj L (rankSmallBounded.inverseImage (supportedSequence z).ι).trW
  let X := L.objPreimage P
  obtain ⟨a, b, hab⟩ := supportedSequenceQuotientHomology_bounded lam hfg z hJ hfin U hU hs X
  refine ⟨a, b, fun q hq ↦ ?_⟩
  exact (hab q hq).of_iso
    ((supportedRankHomology lam hfg z hJ hfin U hU hs q).mapIso (L.objObjPreimageIso P).symm ≪≫
      (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).app X)

/-- 支持つきランク商の Karoubi 包絡へのホモロジー関手の延長。 -/
noncomputable def completedSupportedHomology (q : ℤ) :
    Karoubi (SupportedSequenceRankQuotient (s := s) z) ⥤ LengthSerreQuotient lam s U hU hs :=
  (functorExtension _ _).obj (supportedRankHomology lam hfg z hJ hfin U hU hs q)

instance completedSupportedHomology_additive (q : ℤ) :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs q).Additive := by
  dsimp only [completedSupportedHomology]
  infer_instance

/-- 冪等完備化前の対象では、延長したホモロジーは元のホモロジーと一致する。 -/
noncomputable def completedSupportedHomologyFactors (q : ℤ) :
    toKaroubi _ ⋙ completedSupportedHomology lam hfg z hJ hfin U hU hs q ≅
      supportedRankHomology lam hfg z hJ hfin U hU hs q :=
  karoubiExtensionToCompleteFactors _

/-- 形式的直和因子のホモロジーは、射影が誘導する冪等元の像に同型である。 -/
noncomputable def completedSupportedHomologyImageIso
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) (q : ℤ) :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P ≅
      Abelian.image ((supportedRankHomology lam hfg z hJ hfin U hU hs q).map P.p) :=
  karoubiExtensionImageIso _ P

/-- 形式的な直和因子でもホモロジーの非零次数は有限範囲に入る。 -/
lemma completedSupportedHomology_bounded
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  obtain ⟨a, b, hab⟩ := supportedRankHomology_bounded lam hfg z hJ hfin U hU hs P.X
  refine ⟨a, b, fun q hq ↦ ?_⟩
  let F := completedSupportedHomology lam hfg z hJ hfin U hU hs q
  let r := (karoubiRetract P).map F
  have hz := (hab q hq).of_iso
    ((completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).app P.X)
  rw [IsZero.iff_id_eq_zero, ← r.retract, hz.eq_zero_of_src r.r, comp_zero]

/-- 全体の商の冪等完備化で台をもつ任意の対象を評価するホモロジー関手。 -/
noncomputable def completedRankHomology (q : ℤ) :
    (supportedCompletedRankQuotient (s := s) z).FullSubcategory ⥤
      LengthSerreQuotient lam s U hU hs :=
  (supportedKaroubiEquivalence z).inverse ⋙ completedSupportedHomology lam hfg z hJ hfin U hU hs q

/-- 全支持対象のホモロジーも対象ごとに共通の有限範囲をもつ。 -/
lemma completedRankHomology_bounded
    (P : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj P) :=
  completedSupportedHomology_bounded lam hfg z hJ hfin U hU hs
    ((supportedKaroubiEquivalence z).inverse.obj P)

end SerrePositivity.Asymptotic
