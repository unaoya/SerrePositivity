module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationCompletedInitial
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationCompletedSurjective
public import SerrePositivity.BhattScholze.Semiperfectoid.Cor73PrismComparison
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# S′ の初期包絡の完全化と Corollary 7.3

## 概要
S′ の実初期包絡を完全化し、その商が S′ の perfectoid 化であることと Corollary 7.3 との一致を示す。
## 方針
固定 A_inf から S′ への実全射を使い、完全化の普遍性と唯一の δ-prism 同型を適用する。
## 規約
BS 著者版 Proposition 7.10・Corollary 7.3。零環の枝を残し、Δ との同一視は含めない。
## 使われ方
E3 の S′ の場合の始性と完全化との一致。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open CategoryTheory DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]

/-- 固定 A_inf の θ は、零環も含めて全射。 -/
theorem ainfClassicalTheta_surjective (hR : IsIntegralPerfectoid R p) :
    Function.Surjective (ainfClassicalTheta p R hR) := by
  rw [← ainfClassicalResidueEquiv_theta p R hR]
  exact (ainfClassicalResidueEquiv p R hR).surjective.comp Ideal.Quotient.mk_surjective

/-- 固定 A_inf の θ は選択生成元を零へ送る。 -/
theorem ainfClassicalTheta_generator_zero (hR : IsIntegralPerfectoid R p) :
    ainfClassicalTheta p R hR (ainfClassicalPrism p R hR).generator = 0 := by
  let P := ainfClassicalPrism p R hR
  have h := RingHom.congr_fun (ainfClassicalResidueEquiv_theta p R hR) P.generator
  change ainfClassicalResidueEquiv p R hR (Ideal.Quotient.mk P.ideal P.generator) =
    ainfClassicalTheta p R hR P.generator at h
  have hz : Ideal.Quotient.mk P.ideal P.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [hz, map_zero] at h
  exact h.symm

variable (J : Type u)

/-- 概要：S′ の初期包絡の実完全化は perfectoid 化で、Corollary 7.3 と唯一の δ-prism 同型を持つ。
方針：θ と実商射の全射性、完全化の一意延長、perfectoid 化の比較を組み合わせる。
規約：BS 著者版 Proposition 7.10・Corollary 7.3。零環の枝は明示的に保持する。
使われ方：E3 の S′ 上の始性と完全化比較の古典的な出力。 -/
theorem exists_rootRelationPrismaticPerfection (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R J
    let hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
    let P := ainfClassicalPrism p Base hBase
    let I := Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
    let T := Base ⧸ I
    let S' := CompletedRing p T
    let χ := ((principalCompletionRingCatUnit p (CommRingCat.of T)).hom).comp (Ideal.Quotient.mk I)
    let r := χ.comp (ainfClassicalTheta p Base hBase)
    ∃ hr : Function.Surjective r, r P.generator = 0 ∧
      ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (a : OrientedPrism.Hom P Q)
        (v : S' →+* B ⧸ Q.ideal),
        IsBoundedPrism Q ∧ IsInitialPrismUnit Q v ∧
        (∀ x, v (r x) = Ideal.Quotient.mk Q.ideal (a.toRingHom x)) ∧
        IsPerfectoidization p (classicalPrismPerfectionUnit Q v) ∧
        ((Subsingleton Base ∧ Subsingleton S' ∧ Subsingleton (classicalPrismPerfectionCoefficients Q) ∧
            Subsingleton (classicalPrismPerfectionCoefficients Q ⧸ (classicalPrismPerfection Q).ideal) ∧
            IsClassicalCor73Comparison P (ainfClassicalPrism_perfect p Base hBase) r hr
              (classicalPrismPerfection Q) (classicalPrismPerfectionUnit Q v)) ∨
          (Nontrivial Base ∧ ¬IsUnit (p : ainfClassicalCoefficients p Base ⧸ P.ideal) ∧
            IsClassicalCor73Comparison P (ainfClassicalPrism_perfect p Base hBase) r hr
              (classicalPrismPerfection Q) (classicalPrismPerfectionUnit Q v))) := by
  let Base := rootFamilyBase p R J
  let hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
  let P := ainfClassicalPrism p Base hBase
  let A := ainfClassicalCoefficients p Base
  let I : Ideal Base := Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
  let T := Base ⧸ I
  let S' := CompletedRing p T
  let χ : Base →+* S' := ((principalCompletionRingCatUnit p (CommRingCat.of T)).hom).comp (Ideal.Quotient.mk I)
  let r := χ.comp (ainfClassicalTheta p Base hBase)
  have hr : Function.Surjective r := (rootRelationCompletedQuotientMap_surjective p R J hR).comp
    (ainfClassicalTheta_surjective p Base hBase)
  have hrd : r P.generator = 0 := by
    change χ (ainfClassicalTheta p Base hBase P.generator) = 0
    rw [ainfClassicalTheta_generator_zero, map_zero]
  obtain ⟨w, hw, B, Q, ν, hbQ, hEnv, v, hunit, hinit⟩ := exists_rootRelationCompletedInitial p R J hR
  let a : OrientedPrism.Hom P Q := ⟨ν, hEnv.isDeltaHom, by
    simpa only [RingHom.comp_id] using hEnv.base_hom⟩
  have hv : IsInitialPrismUnit Q v := hinit
  refine ⟨hr, hrd, B, Q, a, v, hbQ, hv, hunit,
    classicalPrismPerfectionUnit_isPerfectoidization Q v hv, ?_⟩
  rcases subsingleton_or_nontrivial Base with hs | hn
  · letI := hs
    have hp : IsUnit (p : Base) := by
      rw [show (p : Base) = 1 from Subsingleton.elim _ _]
      exact isUnit_one
    have hA : Subsingleton A := by
      change Subsingleton (ainfClassicalCoefficients p Base)
      rw [ainfClassicalCoefficients_of_isUnit p Base hp]
      infer_instance
    letI := hA
    have hB : Subsingleton B := ν.codomain_trivial
    letI := hB
    have hPerf : Subsingleton (classicalPrismPerfectionCoefficients Q) :=
      (classicalPrismPerfectionMap Q).toRingHom.codomain_trivial
    letI := hPerf
    letI : Subsingleton S' := χ.codomain_trivial
    exact Or.inl ⟨hs, inferInstance, hPerf, (Ideal.Quotient.mk _).codomain_trivial,
      classicalPrismPerfection_cor73_of_subsingleton P
        (ainfClassicalPrism_perfect p Base hBase) r hr Q v hv⟩
  · letI := hn
    have hpBase : ¬IsUnit (p : Base) := by
      rcases hBase with hs | ⟨hp, _⟩
      · exact False.elim (zero_ne_one (hs.elim _ _))
      · exact hp
    have hp : ¬IsUnit (p : A ⧸ P.ideal) := by
      intro hu
      apply hpBase
      simpa only [map_natCast] using hu.map (ainfClassicalResidueEquiv p Base hBase).toRingHom
    letI : Fact (¬IsUnit (p : A ⧸ P.ideal)) := ⟨hp⟩
    exact Or.inr ⟨hn, hp, classicalPrismPerfection_cor73 P
      (ainfClassicalPrism_perfect p Base hBase) r hr hrd Q v hv⟩

end SerrePositivity.BhattScholze.Semiperfectoid
