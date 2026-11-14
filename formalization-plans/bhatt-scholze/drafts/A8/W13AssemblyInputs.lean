module

import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
import SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison
import SerrePositivity.BhattScholze.IntegralPerfectoidization.FiniteEtale.FiniteEtalePerfectoid
import SerrePositivity.BhattScholze.IntegralPerfectoidization.Completion.IntegralClosureCompletion
import SerrePositivity.BhattScholze.IntegralPerfectoidization.Approximation.IntegralClosureApproximation
import SerrePositivity.BhattScholze.IntegralPerfectoidization.Approximation.IntegralApproximation
import SerrePositivity.BhattScholze.IntegralPerfectoidization.Approximation.PerfectoidFilteredColimit
import SerrePositivity.CommutativeAlgebra.EtaleStratification.Stratification
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalIdeal

/-!
# BS-W13 の接続の型

## 概要
BS 著者版 Theorem 10.9・10.11 の古典的な入力の型を照合する。

## 方針
比較写像の始域、主イデアル、付値環への一意延長、完備性を明示する。
帰納段の連結性の組み合わせには Lemma 10.5 を用いる。

## 規約
perfd の値に関する入力は既存 drafts の定理に置く。

## 使われ方
`AlmostPurityConnectivity.lean` と `IntegralDiscreteness.lean` の組み立て。
-/

noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity SerrePositivity.CommutativeAlgebra SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze.Almost
open SerrePositivity.BhattScholze.Perfectoidization.Derived
open SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories

namespace SerrePositivity.BhattScholze.Draft.W13

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (hR : IsIntegralPerfectoid R p)

private def comparisonArrow {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : ofAlgebra R A ⟶ ofAlgebra R B :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (CommRingCat.hom_ext f.comp_algebraMap)

/-- Theorem 10.9 の一つの分裂主開に対する二つの付値環条件と比較環の完備性。 -/
example [Module.Finite R S] (g : R) (r : ℕ) (e : AwaySplitting R S g r) :
    let C := trivialCoverComparison R S g r e
    ArcOutside R p (comparisonArrow R (sourceToComparison R S g r e))
      (Ideal.span {algebraMap R S g}) ∧
    ArcOutside R p (comparisonArrow R (productToComparison R S g r e))
      (Ideal.span {algebraMap R (Fin r → R) g}) ∧
    IsModuleComplete C (p : C) (ModuleCat.of C C) := by
  let C := trivialCoverComparison R S g r e
  have hc := trivialCoverComparison_isModuleComplete R S p hR g r e
  have hloc := trivialCoverComparison_localization_iso R S g r e
  have hint := trivialCoverComparison_integral R S g r e
  refine ⟨arcOutside_of_integral_of_localization_iso p R _ _ hint.1 hloc.1,
    arcOutside_of_integral_of_localization_iso p R _ _ hint.2 hloc.2, ?_⟩
  simpa only [map_natCast] using (isModuleComplete_algebraMap_iff R C (p : R) C).mpr hc

/-- Theorem 10.11 の比較に Corollary 8.12 を適用する三つの完備性と付値環条件。 -/
example [Module.Finite R S] [Algebra.FinitePresentation R S]
    (g : R) (het : FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let I := Ideal.span {algebraMap R S g}
    let C := (integralClosureCompletion p R S g).right
    IsModuleComplete S (p : S) (ModuleCat.of S S) ∧
    IsModuleComplete C (p : C) (ModuleCat.of C C) ∧
    IsModuleComplete S (p : S) (ModuleCat.of S I) ∧
    ArcOutside R p (completedClosureArrow p R S g inferInstance) I := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  obtain ⟨_, hS, hI, _⟩ :=
    isModuleComplete_finitePresentation_algebra_principal R S (p : R) (algebraMap R S g)
      (hR.isModuleComplete R p)
  rw [map_natCast] at hS hI
  exact ⟨hS, (integralClosureCompletion_isModuleComplete p R S hR g het).1, hI,
    arcOutside_completionRing p R S g inferInstance⟩

/-- Lemma 10.12 の既存結論を draft の層別の三条件として使う。 -/
example [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i : Fin n,
        let I := earlierIdeal g i
        HasEtaleFactorization p (stratumMap (algebraMap R S) I (g i)) ∧
          ((p : StratumRing I (g i)) = 0 ∨ IsUnit (p : StratumRing I (g i))) :=
  exists_finiteEtaleStratification (R := R) (S := S) p hZp

/-- Theorem 10.11 の帰納段で、商側の連結性と主イデアルに関する almost 連結性を合わせる。 -/
example (J : Ideal R) (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M)
    (hq : Derived.IsConnectiveAt R 0 (quotientTensor p hR J M))
    (ha : IsAlmostConnective p R hR J M) : Derived.IsConnectiveAt R 0 M :=
  (connective_iff_almost p hR J hJ M hM).mpr ⟨hq, ha⟩

/-- Theorem 10.11 の各近似で Theorem 10.9 を使う。指定の局所化写像が全単射なら
有限エタール性を各段へ移せる。 -/
example {L A B : Type u} [CommRing L] [CommRing A] [CommRing B]
    [Algebra R L] [Algebra R A] [Algebra R B] [Algebra L A] [Algebra L B]
    [IsScalarTower R L A] [IsScalarTower R L B]
    (g : R) [IsLocalization.Away g L] [Module.Finite L B] [Algebra.Etale L B]
    (f : A →ₐ[R] B) (hf : Function.Bijective f) :
    Module.Finite L A ∧ Algebra.Etale L A := by
  have hc : f.toRingHom.comp (algebraMap L A) = algebraMap L B := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro r
    change f (algebraMap L A (algebraMap R L r)) = algebraMap L B (algebraMap R L r)
    rw [← IsScalarTower.algebraMap_apply R L A, ← IsScalarTower.algebraMap_apply R L B]
    exact f.commutes r
  let f' : A →ₐ[L] B := { __ := f.toRingHom, commutes' := RingHom.congr_fun hc }
  let e := AlgEquiv.ofBijective f' hf
  exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    Algebra.Etale.of_equiv e.symm⟩

#check exists_finitePresentation_approximation_fixedLocalization
#check integral_isFilteredColimit_finitePresentation
#check isIntegralPerfectoid_completedFilteredColimit
#check isIntegralPerfectoid_of_finiteEtale

end SerrePositivity.BhattScholze.Draft.W13
