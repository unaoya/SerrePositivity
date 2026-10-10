module

public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.Asymptotic.FreeSequenceBaseChange

/-!
# ランク商への係数変更の降下

行列による係数変更は共通有界性と小さいランクの条件を保つので、
冪等完備化前の Verdier 商に降りる。商関手との自然同型も構成する。
ここでの係数変更と通常の導来テンソル積の比較、および Karoubi 包絡への
三角構造の延長は別途必要である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S)

omit [Nontrivial R] [Nontrivial S] in
/-- 小さいランクの共通有界複体は係数変更で保たれる。 -/
lemma changeRing_rankSmallComplex (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : rankSmallComplex K) :
    rankSmallComplex (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  refine ⟨?_, hK.2⟩
  obtain ⟨a, b, ha, hb⟩ := hK.1
  exact ⟨a, b, inferInstanceAs (CochainComplex.IsStrictlyGE
    (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) a),
    inferInstanceAs (CochainComplex.IsStrictlyLE
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) b)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [Nontrivial R] [Nontrivial S] in
/-- 小さいランクの代表をもつ有界ホモトピー対象は、係数変更後も同じ性質をもつ。 -/
lemma changeRing_rankSmallBounded (X : SequenceHomotopy R s) (hX : rankSmallBounded X) :
    rankSmallBounded ((mapBoundedHomotopy (FreeSequence.changeRing φ)).obj X) := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := hX
  obtain ⟨K, hK⟩ := hY
  refine ⟨_, (rankSmallHomotopy_quotient _).2 (changeRing_rankSmallComplex φ K hK),
    ⟨((FreeSequence.changeRing φ).mapHomotopyCategory (.up ℤ)).mapIso e⟩⟩

omit [Nontrivial R] in
/-- ランク商への係数変更は、元のランク商の分母を可逆にする。 -/
lemma changeRing_inverts_rankSmall :
    (rankSmallBounded (R := R) (s := s)).trW.IsInvertedBy
      (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor) := by
  let F := mapBoundedHomotopy (FreeSequence.changeRing (s := s) φ)
  let P := rankSmallBounded (R := S) (s := s)
  have h : rankSmallBounded (R := R) (s := s) ≤ P.inverseImage F :=
    fun X hX ↦ changeRing_rankSmallBounded φ X hX
  intro X Y f hf
  exact P.inverseImage_trW_isInverted F P.trW.Q f
    (ObjectProperty.trW_monotone h f hf)

/-- 冪等完備化前のランク商に誘導される係数変更関手。 -/
@[implicit_reducible]
noncomputable def rankQuotientChangeRing : SequenceRankQuotient R s ⥤ SequenceRankQuotient S s :=
  Localization.lift
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (changeRing_inverts_rankSmall φ) sequenceRankQuotientFunctor

/-- 係数変更を商に降ろす操作は、標準商関手と自然同型を介して可換である。 -/
noncomputable def rankQuotientChangeRing_fac :
    sequenceRankQuotientFunctor ⋙ rankQuotientChangeRing (s := s) φ ≅
      mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor :=
  Localization.fac _ (changeRing_inverts_rankSmall φ) _

noncomputable instance : Localization.Lifting
    (sequenceRankQuotientFunctor (R := R) (s := s)) (rankSmallBounded (R := R) (s := s)).trW
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (rankQuotientChangeRing φ) :=
  ⟨rankQuotientChangeRing_fac φ⟩

noncomputable instance : (rankQuotientChangeRing (s := s) φ).CommShift ℤ :=
  Functor.commShiftOfLocalization sequenceRankQuotientFunctor
    (rankSmallBounded (R := R) (s := s)).trW ℤ
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (rankQuotientChangeRing φ)

instance : NatTrans.CommShift (rankQuotientChangeRing_fac (s := s) φ).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (sequenceRankQuotientFunctor (R := R) (s := s)) (rankSmallBounded (R := R) (s := s)).trW ℤ
    (mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ sequenceRankQuotientFunctor)
    (rankQuotientChangeRing φ)

/-- ランク商に降ろした係数変更は三角関手である。 -/
instance : (rankQuotientChangeRing (s := s) φ).IsTriangulated := by
  let := Localization.essSurj_mapArrow
    (sequenceRankQuotientFunctor (R := R) (s := s)) (rankSmallBounded (R := R) (s := s)).trW
  exact Functor.isTriangulated_of_precomp_iso (rankQuotientChangeRing_fac φ)

end SerrePositivity.Asymptotic
