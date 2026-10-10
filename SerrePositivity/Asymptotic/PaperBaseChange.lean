module

public import SerrePositivity.Asymptotic.PaperRankEvaluation
public import SerrePositivity.Asymptotic.CompletedK0Comparison

/-! # 論文の支持圏上の係数変更と K₀ 評価 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 支持圏の三角同値に沿って、論文の圏上に移した係数変更。 -/
noncomputable abbrev paperSupportedChangeRing :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤
      (paperSupportedRank (s := s) (φ ∘ z)).FullSubcategory :=
  (paperSupportedToKaroubi z).functor ⋙
    (functorExtension₂ _ _).obj (supportedRankChangeRing φ z) ⋙
      (paperSupportedToKaroubi (φ ∘ z)).inverse

/-- 係数変更の前後で、支持つき商を用いた計算モデルとの比較が可換。 -/
noncomputable def paperSupportedChangeRingFactors :
    paperSupportedChangeRing (s := s) φ z ⋙ (paperSupportedToKaroubi (φ ∘ z)).functor ≅
      (paperSupportedToKaroubi z).functor ⋙
        (functorExtension₂ _ _).obj (supportedRankChangeRing φ z) :=
  isoWhiskerLeft ((paperSupportedToKaroubi z).functor ⋙
    (functorExtension₂ _ _).obj (supportedRankChangeRing φ z))
    (paperSupportedToKaroubi (φ ∘ z)).counitIso

/-- 論文の支持圏でも二段階の係数変更と直接の係数変更が一致する。 -/
noncomputable def paperSupportedChangeRingCompIso
    {T : Type u} [CommRing T] [Nontrivial T] (ψ : S →+* T) :
    paperSupportedChangeRing (s := s) φ z ⋙ paperSupportedChangeRing ψ (φ ∘ z) ≅
      paperSupportedChangeRing (ψ.comp φ) z :=
  isoWhiskerRight (paperSupportedChangeRingFactors φ z)
    ((functorExtension₂ _ _).obj (supportedRankChangeRing ψ (φ ∘ z)) ⋙
      (paperSupportedToKaroubi (ψ ∘ φ ∘ z)).inverse) ≪≫
    isoWhiskerLeft (paperSupportedToKaroubi z).functor
      (isoWhiskerRight (completedSupportedChangeRingCompIso φ ψ z)
        (paperSupportedToKaroubi ((ψ.comp φ) ∘ z)).inverse)

/-- 二段階の係数変更は K₀ 上でも直接の係数変更と同じ写像を与える。 -/
lemma paperSupportedChangeRingK0_comp
    {T : Type u} [CommRing T] [Nontrivial T] (ψ : S →+* T) :
    (TriangulatedK0.map (paperSupportedChangeRing (s := s) ψ (φ ∘ z))).comp
      (TriangulatedK0.map (paperSupportedChangeRing (s := s) φ z)) =
        TriangulatedK0.map (paperSupportedChangeRing (s := s) (ψ.comp φ) z) := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk]
  exact TriangulatedK0.mk_iso ((paperSupportedChangeRingCompIso φ z ψ).app X)

variable {J : Ideal R} {I : Ideal S} (lam : NormalizedLength R J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 論文の圏の Euler 評価を計算モデルへ移す。 -/
lemma paperRankEulerK0_viaSupported :
    paperRankEulerK0 lam hfg z hJ hfin U hU hs =
      (completedSupportedEulerK0 lam hfg z hJ hfin U hU hs).comp
        (TriangulatedK0.map (paperSupportedToKaroubi z).functor) := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [paperRankEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedRankEulerK0_mk, completedSupportedEulerK0_mk]
  rfl

set_option maxHeartbeats 800000 in
-- 支持部分圏、局所化、Karoubi 延長の合成に現れる型の比較に必要。
/-- 論文の圏の K₀ 上の階数倍公式。有限版の比較と A 側の冪等完備性から従う。 -/
theorem paperRankEulerK0_changeRing
    [IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z)]
    (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology q) ≠ ⊤)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P) :
    (paperRankEulerK0 mu hIfg (φ ∘ z) hI hfinS U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing φ z)) =
        c • paperRankEulerK0 lam hfg z hJ hfin U hU hs := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk, AddMonoidHom.smul_apply,
    smul_eq_mul]
  rw [paperRankEulerK0_viaSupported, paperRankEulerK0_viaSupported]
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk]
  simp only [completedSupportedEulerK0_mk]
  exact (completedSupportedEuler_iso mu hIfg (φ ∘ z) hI hfinS U hU hs
    ((paperSupportedChangeRingFactors φ z).app X)).trans
      (completedSupportedEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc
        ((paperSupportedToKaroubi z).functor.obj X))

end SerrePositivity.Asymptotic
