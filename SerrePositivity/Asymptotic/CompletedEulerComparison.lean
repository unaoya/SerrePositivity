module

public import SerrePositivity.Asymptotic.RankEulerComparison

/-!
# 冪等完備化後の Euler 比較

始域の支持つきランク商が冪等完備ならば、有限版の Euler 比較は
Karoubi 包絡の任意の対象にも成り立つ。値域の冪等完備性は要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} {J : Ideal R} {I : Ideal S}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

/-- A 側の一様代表により、Euler の階数倍公式を任意の形式的直和因子へ拡張する。 -/
theorem completedSupportedEuler_changeRing
    [IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z)]
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology q) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P)
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEuler mu hIfg (φ ∘ z) hI hfinS U hU hs
      (((functorExtension₂ _ _).obj (supportedRankChangeRing φ z)).obj X) =
      c * completedSupportedEuler lam hfg z hJ hfin U hU hs X := by
  let F := supportedRankChangeRing (s := s) φ z
  let E := (functorExtension₂ _ _).obj F
  obtain ⟨Y, ⟨iY⟩⟩ := Functor.EssSurj.mem_essImage
    (toKaroubi (SupportedSequenceRankQuotient (s := s) z)) X
  calc
    _ = completedSupportedEuler mu hIfg (φ ∘ z) hI hfinS U hU hs
        ((toKaroubi _).obj (F.obj Y)) :=
      completedSupportedEuler_iso _ _ _ _ _ _ _ _
        (E.mapIso iY.symm ≪≫
          ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).app Y)
    _ = supportedRankEuler mu hIfg (φ ∘ z) hI hfinS U hU hs (F.obj Y) :=
      completedSupportedEuler_obj _ _ _ _ _ _ _ _ _
    _ = c * supportedRankEuler lam hfg z hJ hfin U hU hs Y :=
      supportedRankEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc Y
    _ = _ := congrArg (c * ·)
      ((completedSupportedEuler_obj lam hfg z hJ hfin U hU hs Y).symm.trans
        (completedSupportedEuler_iso lam hfg z hJ hfin U hU hs iY))

end SerrePositivity.Asymptotic
