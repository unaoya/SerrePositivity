module
public import SerrePositivity.CategoryTheory.HomotopyProperty

public import SerrePositivity.Asymptotic.SequenceComplex
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# 小さいランクの複体による Verdier 商

共通有界な自由列のホモトピー圏を、各次数のランクが `o(s)` となる複体で割る。
ランク条件のシフト・錐への安定性を証明して、実際の Verdier 局所化を構成する。
ここでは冪等完備化より前の商を扱う。論文の `D_R/N_R` との比較と、
商の Karoubi 包絡への三角構造の延長は別途必要である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter Asymptotics
open scoped ZeroObject

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

namespace FreeSequence

/-- 自由列の同型は、各段のランクを保つ。 -/
lemma rank_eq_of_iso {X Y : FreeSequence R s} (e : X ≅ Y) (n : ℕ) :
    X.rank n = Y.rank n := by
  have h := ((evaluation n).mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank R (Fin (X.rank n) → R) =
    Module.finrank R (Fin (Y.rank n) → R) at h
  simpa only [Module.finrank_fin_fun] using h

/-- 零対象の各段のランクは零である。 -/
lemma rank_eq_zero_of_isZero (X : FreeSequence R s) (hX : IsZero X) (n : ℕ) :
    X.rank n = 0 :=
  rank_eq_of_iso (hX.iso zero_isZero) n

/-- 二項直和のランクは各段で加法的である。 -/
lemma rank_biprod (X Y : FreeSequence R s) (n : ℕ) :
    (X ⊞ Y).rank n = X.rank n + Y.rank n := by
  exact rank_eq_of_iso (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y)
    (isBinaryBilimitOfTotal (sumBicone X Y) (sumBicone_total X Y)).isLimit) n

/-- 任意の有限自由加群列は、ランク条件を満たす標準自由列で各段同型に表せる。 -/
lemma exists_model (M : ℕ → ModuleCat.{u} R)
    [∀ n, Module.Free R (M n)] [∀ n, Module.Finite R (M n)]
    (hM : (fun n ↦ (Module.finrank R (M n) : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ X : FreeSequence R s, ∀ n, Nonempty ((evaluation n).obj X ≅ M n) :=
  ⟨⟨fun n ↦ Module.finrank R (M n), hM⟩,
    fun n ↦ ⟨(Module.finBasis R (M n)).equivFun.symm.toModuleIso⟩⟩

end FreeSequence

/-- 共通有界で、各次数のランク列が通常の `o(s)` であるという条件。 -/
def rankSmallComplex : ObjectProperty (CochainComplex (FreeSequence R s) ℤ) :=
  fun K ↦ strictlyBoundedComplex (FreeSequence R s) K ∧
    ∀ i, (fun n ↦ ((K.X i).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))

/-- ランクが小さい代表複体をもつホモトピー圏の対象。 -/
def rankSmallHomotopy : ObjectProperty (HomotopyCategory (FreeSequence R s) (.up ℤ)) :=
  rankSmallComplex.strictMap (HomotopyCategory.quotient _ _)

omit [Nontrivial R] in
/-- ランク条件はホモトピー圏の代表複体について読める。 -/
@[simp] lemma rankSmallHomotopy_quotient (K : CochainComplex (FreeSequence R s) ℤ) :
    rankSmallHomotopy ((HomotopyCategory.quotient _ _).obj K) ↔ rankSmallComplex K :=
  homotopyProperty_strictMap_quotient rankSmallComplex K

instance : (rankSmallHomotopy (R := R) (s := s)).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    Functor.map_isZero _ (isZero_zero _), by
      rw [rankSmallHomotopy_quotient]
      refine ⟨⟨0, 0, inferInstance, inferInstance⟩, ?_⟩
      intro i
      have hz (n : ℕ) : (((0 : CochainComplex (FreeSequence R s) ℤ).X i).rank n) = 0 :=
        FreeSequence.rank_eq_zero_of_isZero _
          ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)) n
      simpa only [hz, Nat.cast_zero] using (isLittleO_zero (fun n ↦ (s n : ℝ)) atTop)⟩

instance : (rankSmallHomotopy (R := R) (s := s)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        rw [rankSmallHomotopy_quotient] at hK
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          rankSmallHomotopy_quotient]
        refine ⟨?_, fun i ↦ hK.2 (i + n)⟩
        exact strictlyBoundedComplex_shift _ hK.1 n }

/-- 小さいランクの複体の間の射の錐も、各次数で小さいランクをもつ。 -/
lemma rankSmallComplex_mappingCone {K L : CochainComplex (FreeSequence R s) ℤ}
    (f : K ⟶ L) (hK : rankSmallComplex K) (hL : rankSmallComplex L) :
    rankSmallComplex (CochainComplex.mappingCone f) := by
  refine ⟨strictlyBoundedComplex_mappingCone _ f hK.1 hL.1, fun i ↦ ?_⟩
  have he := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)
  have hr (n : ℕ) := FreeSequence.rank_eq_of_iso he n
  simp only [FreeSequence.rank_biprod] at hr
  simp_rw [show ∀ n, ((CochainComplex.mappingCone f).X i).rank n =
    (K.X (i + 1)).rank n + (L.X i).rank n from hr, Nat.cast_add]
  exact (hK.2 (i + 1)).add (hL.2 i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (rankSmallHomotopy (R := R) (s := s)).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (rankSmallHomotopy_quotient)
    (fun f => rankSmallComplex_mappingCone f)

instance : (rankSmallHomotopy (R := R) (s := s)).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 共通有界ホモトピー圏における小さいランクの三角部分圏。 -/
def rankSmallBounded : ObjectProperty (SequenceHomotopy R s) :=
  rankSmallHomotopy.isoClosure.inverseImage (boundedHomotopyInclusion _)

instance : (rankSmallBounded (R := R) (s := s)).IsClosedUnderIsomorphisms :=
  inferInstanceAs (rankSmallHomotopy.isoClosure.inverseImage
    (boundedHomotopyInclusion _)).IsClosedUnderIsomorphisms

instance : (rankSmallBounded (R := R) (s := s)).IsTriangulated :=
  inferInstanceAs
    (rankSmallHomotopy.isoClosure.inverseImage (boundedHomotopyInclusion _)).IsTriangulated

/-- 冪等完備化に先立つ、共通有界な自由列のランク商。 -/
abbrev SequenceRankQuotient (R : Type u) [CommRing R] [Nontrivial R] (s : ℕ → ℕ) :=
  (rankSmallBounded (R := R) (s := s)).trW.Localization

/-- 小さいランクの対象を消す標準的な Verdier 商関手。 -/
abbrev sequenceRankQuotientFunctor : SequenceHomotopy R s ⥤ SequenceRankQuotient R s :=
  (rankSmallBounded (R := R) (s := s)).trW.Q

/-- 小さいランクの有界対象は、構成した Verdier 商で零になる。 -/
lemma sequenceRankQuotient_isZero (X : SequenceHomotopy R s) (hX : rankSmallBounded X) :
    IsZero (sequenceRankQuotientFunctor.obj X) := by
  let P := rankSmallBounded (R := R) (s := s)
  have hf : P.trW (0 : (0 : SequenceHomotopy R s) ⟶ X) :=
    ⟨X, 𝟙 X, 0, contractible_distinguished₁ X, hX⟩
  have := Localization.inverts P.trW.Q P.trW _ hf
  exact IsZero.of_iso (P.trW.Q.map_isZero (isZero_zero _))
    (asIso (P.trW.Q.map (0 : (0 : SequenceHomotopy R s) ⟶ X))).symm

/-- 小さいランクの複体を有界ホモトピー圏に入れると、そのランク商での像は零になる。 -/
lemma sequenceRankQuotient_smallComplex_isZero
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : rankSmallComplex K) :
    IsZero (sequenceRankQuotientFunctor.obj
      ⟨(HomotopyCategory.quotient _ _).obj K,
        (boundedHomotopyProperty_quotient _ K).2 hK.1⟩) := by
  apply sequenceRankQuotient_isZero
  exact ⟨(HomotopyCategory.quotient _ _).obj K,
    (rankSmallHomotopy_quotient K).2 hK, ⟨Iso.refl _⟩⟩

end SerrePositivity.Asymptotic
