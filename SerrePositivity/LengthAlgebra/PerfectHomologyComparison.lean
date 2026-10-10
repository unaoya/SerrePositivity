module

public import SerrePositivity.LengthAlgebra.FiniteQuotientEquivalence
public import SerrePositivity.LengthAlgebra.PerfectVanishing

/-! # 二つの長さの商で計算する perfect ホモロジーの比較

消滅を扱う大きな商のホモロジーは、Koszul 有限性の下で有限長さ部分に値をもつ。
有限商による Euler 評価との対応を、圏同値に沿う自然同型として与える。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (hfin : KoszulFinite lam z)

/-- 有限商のホモロジーを大きな商へ送ると、直接構成したホモロジーに一致する。 -/
noncomputable def perfectQuotientHomologyInclusionIso (q : ℤ) :
    perfectQuotientHomology lam hfg z hJ hfin q ⋙ finiteQuotientInclusion lam ≅
      perfectLengthHomology lam hfg z hJ q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (perfectFiniteHomology lam hfg z hJ hfin q)
      (finiteQuotientInclusionIso lam) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (show perfectFiniteHomology lam hfg z hJ hfin q ⋙ finiteTorsionInclusion lam ≅
        perfectTorsionHomology hfg z hJ q from Iso.refl _) (lengthQuotientFunctor lam)

include hfin in
/-- Koszul 有限性から、大きな商のホモロジーが有限部分に属することを確認する。 -/
lemma perfectLengthHomology_mem_finitePart (X : SupportedPerfectHomotopy z) (q : ℤ) :
    finiteLengthPart lam ((perfectLengthHomology lam hfg z hJ q).obj X) :=
  (perfectModuleHomology_mem lam hfg z hJ hfin X q).2

/-- 大きな商の有限部分に値をもつホモロジー関手。 -/
noncomputable def perfectFinitePartHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ FiniteLengthPart lam :=
  (finiteLengthPart lam).lift (perfectLengthHomology lam hfg z hJ q)
    (fun X ↦ perfectLengthHomology_mem_finitePart lam hfg z hJ hfin X q)

instance perfectFinitePartHomology_additive (q : ℤ) :
    (perfectFinitePartHomology lam hfg z hJ hfin q).Additive := by
  dsimp only [perfectFinitePartHomology]
  infer_instance

instance perfectFinitePartHomology_isHomological (q : ℤ) :
    (perfectFinitePartHomology lam hfg z hJ hfin q).IsHomological where
  exact T hT := by
    apply (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthPart lam).ι).mp
    exact (perfectLengthHomology lam hfg z hJ q).map_distinguished_exact T hT

/-- 二つの有限値ホモロジー関手は、構成した圏同値に沿って自然に同型となる。 -/
noncomputable def perfectHomologyEquivalenceIso (q : ℤ) :
    perfectQuotientHomology lam hfg z hJ hfin q ⋙ (finiteQuotientEquivalence lam).functor ≅
      perfectFinitePartHomology lam hfg z hJ hfin q :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _
    ((perfectQuotientHomologyInclusionIso lam hfg z hJ hfin q).app X)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (perfectQuotientHomologyInclusionIso lam hfg z hJ hfin q).hom.naturality f)

/-- 消滅を有限商と大きな商の間で移せる。 -/
lemma perfectQuotientHomology_isZero_iff_lengthHomology
    (X : SupportedPerfectHomotopy z) (q : ℤ) :
    IsZero ((perfectQuotientHomology lam hfg z hJ hfin q).obj X) ↔
      IsZero ((perfectLengthHomology lam hfg z hJ q).obj X) := by
  let i := (perfectQuotientHomologyInclusionIso lam hfg z hJ hfin q).app X
  exact ⟨fun h ↦ ((finiteQuotientInclusion lam).map_isZero h).of_iso i.symm,
    fun h ↦ IsZero.of_full_of_faithful_of_isZero (finiteQuotientInclusion lam) _ (h.of_iso i)⟩

/-- 各次数の長さは、二つの評価先で一致する。 -/
lemma perfectFinitePartHomology_length (X : SupportedPerfectHomotopy z) (q : ℤ) :
    finitePartLength lam ((perfectFinitePartHomology lam hfg z hJ hfin q).obj X) =
      quotientLength lam ((perfectQuotientHomology lam hfg z hJ hfin q).obj X) := by
  rw [← finitePartLength_iso lam ((perfectHomologyEquivalenceIso lam hfg z hJ hfin q).app X)]
  exact finiteQuotientEquivalence_length_toReal lam _

/-- 有限部分での零対象判定も、従来の有限商での判定と一致する。 -/
lemma perfectFinitePartHomology_isZero_iff (X : SupportedPerfectHomotopy z) (q : ℤ) :
    IsZero ((perfectFinitePartHomology lam hfg z hJ hfin q).obj X) ↔
      IsZero ((perfectQuotientHomology lam hfg z hJ hfin q).obj X) := by
  rw [← finitePartLength_eq_zero_iff, ← quotientLength_eq_zero_iff,
    perfectFinitePartHomology_length]

noncomputable instance perfectFinitePartHomology_shiftSequence :
    (perfectFinitePartHomology lam hfg z hJ hfin 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- 圏同値を通して、共通 Euler 理論に必要な対象ごとの有界性も移る。 -/
lemma perfectFinitePartHomology_shift_bounded (X : SupportedPerfectHomotopy z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((perfectFinitePartHomology lam hfg z hJ hfin 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := perfectQuotientHomology_shift_bounded lam hfg z hJ hfin X
  exact ⟨a, b, fun q hq ↦ (perfectFinitePartHomology_isZero_iff lam hfg z hJ hfin
    ((shiftFunctor _ q).obj X) 0).mpr (hab q hq)⟩

/-- 有限部分へ移したホモロジーで共通 Euler 和を計算しても、既存の評価と一致する。 -/
theorem perfectEuler_eq_finitePartEuler (X : SupportedPerfectHomotopy z) :
    perfectEuler lam hfg z hJ hfin X =
      homologicalEuler (finitePartLength lam)
        (perfectFinitePartHomology lam hfg z hJ hfin 0) X := rfl

/-- 大きな商の有限部分で共通定理を適用して得る K₀ 評価は、既存の評価に一致する。 -/
theorem perfectEulerK0_eq_finitePartEulerK0 :
    perfectEulerK0 lam hfg z hJ hfin =
      homologicalEulerK0 (finitePartLength lam) (finitePartLength_iso lam)
        (finitePartLength_add lam) (perfectFinitePartHomology lam hfg z hJ hfin 0)
        (fun X hX ↦ (finitePartLength_eq_zero_iff lam X).mpr hX)
        (perfectFinitePartHomology_shift_bounded lam hfg z hJ hfin) := by
  apply TriangulatedK0.hom_ext
  intro X
  rw [perfectEulerK0_mk, homologicalEulerK0_mk, perfectEuler_eq_finitePartEuler]

end SerrePositivity.LengthAlgebra
