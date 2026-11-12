module

public import SerrePositivity.BhattScholze.Prismatic.FiniteEnvelopeDiagram
public import SerrePositivity.BhattScholze.Semiperfectoid.RootFamilyPerfectoid
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationFiniteAmbient
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationSubsetRaw
public import SerrePositivity.CommutativeAlgebra.DirectLimitRelations
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionUniformBound

/-!
# S′ の共通指数と実完備化への全射

## 概要
通常の全初期関係商の指数1から、根付き基底から S′ への全射と古典的完備化比較を得る。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## RootRelationZeroQuotientBound -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Andre DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)

/-- 概要：全初期変数の通常商にも、有限段に共通する指数1が有効。
方針：有限段のイデアルを座標で比較し、生の関係商余極限の同型を使う。
規約：BS 著者版 Proposition 7.10。零環と無限の添字を含む。
使われ方：S′ の実完備化の単位の全射性。 -/
theorem rootRelationZeroQuotient_torsion_bound_one (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R J
    let T := Base ⧸ Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
    ∀ n : ℕ, ∀ x : T, (p : T) ^n * x = 0 → (p : T) * x = 0 := by
  let Base := rootFamilyBase p R J
  let z := fun j => rootFamilyVariable p R J j 0
  have hF (F : Finset J) (n : ℕ) (x : FiniteRelationStage z F)
      (hx : (p : FiniteRelationStage z F) ^n * x = 0) : (p : FiniteRelationStage z F) ^1 * x = 0 := by
    let ι : Fin (Fintype.card F) → J := fun i => (finiteEnvelopeEnumeration F i).val
    have hrange : Set.range ι = (F : Set J) := by
      ext j
      constructor
      · rintro ⟨i, rfl⟩
        exact (finiteEnvelopeEnumeration F i).property
      · intro hj
        refine ⟨(finiteEnvelopeEnumeration F).symm ⟨j, hj⟩, ?_⟩
        exact congrArg Subtype.val ((finiteEnvelopeEnumeration F).apply_symm_apply ⟨j, hj⟩)
    have hI : (rootRelationSubsetRawIdeal p R J (Set.range ι)).map (rootFamilyUnit p R J) =
        finiteRelationIdeal z F := by
      change rootRelationSubsetBaseIdeal p R J (Set.range ι) = _
      rw [rootRelationSubsetBaseIdeal_eq, hrange]
      rfl
    let e : rootRelationFiniteAmbientQuotient p R J ι ≃+* FiniteRelationStage z F := Ideal.quotEquivOfEq hI
    have hx' : (p : rootRelationFiniteAmbientQuotient p R J ι) ^n * e.symm x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg e.symm hx
    have h := rootRelationFiniteAmbientQuotient_torsion_bound_one p R J ι hR n (e.symm x) hx'
    simpa only [map_mul, map_natCast, map_zero, e.apply_symm_apply, pow_one] using congrArg e h
  let e := finiteRelationColimitEquiv z
  change ∀ (n : ℕ) (x : Base ⧸ Ideal.span (Set.range z)),
    (p : Base ⧸ Ideal.span (Set.range z)) ^n * x = 0 → (p : Base ⧸ Ideal.span (Set.range z)) * x = 0
  intro n x hx
  apply e.symm.injective
  have hx' : (p : FiniteRelationColimit z) ^n * e.symm x = 0 := by
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg e.symm hx
  have h := ringDirectLimit_uniform_torsion_bound (FiniteRelationStage z)
    (fun _ _ h => finiteRelationMap z h) p 1 hF n (e.symm x) hx'
  simpa only [map_mul, map_natCast, map_zero, pow_one] using h

end SerrePositivity.BhattScholze.Semiperfectoid

end

/-! ## RootRelationCompletedSurjective -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open DerivedCompletion CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)

/-- 概要：根付き基底から S′ の実 H⁰ への単位付き商射は全射。
方針：前完備性は通常商へ移り、そのねじれ指数1を使って実完備化と比較する。
規約：BS 著者版 Proposition 7.10・Corollary 7.3。零環を含む。
使われ方：Corollary 7.3 の r の全射性の入力。 -/
theorem rootRelationCompletedQuotientMap_surjective (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R J
    let I := Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
    let T := Base ⧸ I
    Function.Surjective (((principalCompletionRingCatUnit p (CommRingCat.of T)).hom).comp
      (Ideal.Quotient.mk I)) := by
  let Base := rootFamilyBase p R J
  let I : Ideal Base := Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
  let T := Base ⧸ I
  have hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
  have hc : IsAdicComplete (Ideal.span {(p : Base)}) Base := by
    rcases hBase with hs | ⟨_, hc, _⟩
    · letI := hs
      infer_instance
    · exact hc
  letI := hc
  have hpre : IsPrecomplete (Ideal.span {(p : Base)}) T :=
    isPrecomplete_of_surjective (Ideal.span {(p : Base)}) (Ideal.Quotient.mkₐ Base I).toLinearMap
      Ideal.Quotient.mk_surjective
  have hpreT : IsPrecomplete (Ideal.span {(p : T)}) T := by
    have h := (IsPrecomplete.map_algebraMap_iff (I := Ideal.span {(p : Base)}) (S := T) (M := T)).mpr hpre
    have hp : algebraMap Base T (p : Base) = (p : T) := map_natCast (algebraMap Base T) p
    simpa only [Ideal.map_span, Set.image_singleton, hp] using h
  letI := hpreT
  have hb : ∃ N : ℕ, ∀ (n : ℕ) (x : T), (p : T) ^n * x = 0 → (p : T) ^N * x = 0 :=
    ⟨1, fun n x hx => by simpa only [pow_one] using rootRelationZeroQuotient_torsion_bound_one p R J hR n x hx⟩
  have h := principalCompletionUnit_surjective_of_precomplete T (p : T) hb
  have h' : Function.Surjective (principalCompletionRingCatUnit p (CommRingCat.of T)).hom := h
  exact h'.comp Ideal.Quotient.mk_surjective


/-- 概要：S′ の実 H⁰ は通常の初期関係商の古典的 p 完備化と単位を保って同型。
方針：通常商の指数1を既存の有界主元完備化比較へ渡す。
規約：BS 著者版 Proposition 7.10。通常商そのものとの同一視ではない。
使われ方：drafts の completionRing と古典的な S′ の比較。 -/
theorem exists_rootRelationCompletedAdicEquiv (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R J
    let T := Base ⧸ Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
    ∃ e : CompletedRing p T ≃+* AdicCompletion (Ideal.span {(p : T)}) T,
      ∀ t : T, e ((principalCompletionRingCatUnit p (CommRingCat.of T)).hom t) =
        AdicCompletion.of (Ideal.span {(p : T)}) T t := by
  let Base := rootFamilyBase p R J
  let T := Base ⧸ Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
  letI := principalCompletionCommRing T (p : T)
  letI := principalCompletionAlgebra T (p : T)
  have hb : ∃ N : ℕ, ∀ (n : ℕ) (x : T), (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0 :=
    ⟨1, fun n x hx => by simpa only [pow_one] using rootRelationZeroQuotient_torsion_bound_one p R J hR n x hx⟩
  let e := Andre.Transfinite.boundedPrincipalCompletionAdicAlgEquiv T (p : T) hb
  exact ⟨e.toRingEquiv, fun t => e.commutes t⟩

end SerrePositivity.BhattScholze.Semiperfectoid

end
