module

public import SerrePositivity.Asymptotic.LengthBoundedSequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# 複体の族のホモロジーと切り詰め

各次数で長さが一様に制限されていれば、標準切り詰め後にも同じ条件が成立する。
切り詰めの境界の内側はホモロジー同型、外側は零対象として処理する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)
  (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 複体の族の第 q ホモロジーを加群列とみなす。 -/
noncomputable abbrev familyHomology (q : ℤ) : ModuleSequence R :=
  Discrete.functor (fun n ↦ (K n).homology q)

/-- 全成分が零なら、ホモロジーの加群列も零。 -/
lemma familyHomology_isZero (q : ℤ) (h : ∀ n, IsZero ((K n).homology q)) :
    IsZero (familyHomology K q) := by
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact (h n.as).eq_of_src _ _

/-- 非正切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncLE_prop
    (Q : ObjectProperty (ModuleSequence R)) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    (hK : ∀ q, Q (familyHomology K q)) (b q : ℤ) :
    Q (familyHomology (fun n ↦ (K n).truncLE b) q) := by
  by_cases hq : q ≤ b
  · have (n : ℕ) : QuasiIsoAt ((K n).ιTruncLE b) q := (K n).quasiIsoAt_ιTruncLE b q hq
    exact (Q).prop_of_iso
      (Discrete.natIso (fun n ↦ (isoOfQuasiIsoAt ((K n.as).ιTruncLE b) q).symm))
      (hK q)
  · apply (Q).prop_of_isZero
    exact familyHomology_isZero _ q (fun n ↦
      ((K n).truncLE b).exactAt_of_isLE b q (by omega) |>.isZero_homology)

/-- 非負切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncGE_prop
    (Q : ObjectProperty (ModuleSequence R)) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    (hK : ∀ q, Q (familyHomology K q)) (a q : ℤ) :
    Q (familyHomology (fun n ↦ (K n).truncGE a) q) := by
  by_cases hq : a ≤ q
  · have (n : ℕ) : QuasiIsoAt ((K n).πTruncGE a) q := (K n).quasiIsoAt_πTruncGE a q hq
    exact (Q).prop_of_iso
      (Discrete.natIso (fun n ↦ isoOfQuasiIsoAt ((K n.as).πTruncGE a) q)) (hK q)
  · apply (Q).prop_of_isZero
    exact familyHomology_isZero _ q (fun n ↦
      ((K n).truncGE a).exactAt_of_isGE a q (by omega) |>.isZero_homology)

/-- 非正切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncLE_lengthBounded
    (hK : ∀ q, lengthBoundedSequence lam s (familyHomology K q)) (b q : ℤ) :
    lengthBoundedSequence lam s (familyHomology (fun n ↦ (K n).truncLE b) q) :=
  familyHomology_truncLE_prop K (lengthBoundedSequence lam s) hK b q

/-- 非負切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncGE_lengthBounded
    (hK : ∀ q, lengthBoundedSequence lam s (familyHomology K q)) (a q : ℤ) :
    lengthBoundedSequence lam s (familyHomology (fun n ↦ (K n).truncGE a) q) :=
  familyHomology_truncGE_prop K (lengthBoundedSequence lam s) hK a q

variable [HasDerivedCategory (ModuleCat.{u} R)]

/-- 複体の族とその導来像とのホモロジーの比較。 -/
noncomputable def familyDerivedHomologyIso (q : ℤ) :
    Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj
      (DerivedCategory.Q.obj (K n))) ≅ familyHomology K q :=
  Discrete.natIso (fun n ↦ (DerivedCategory.homologyFunctorFactors _ q).app (K n.as))

end SerrePositivity.Asymptotic
