module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationRawRegular
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationSubsetRaw
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionUniformBound

/-!
# 任意の根付き基底上の有限初期関係

## 概要
任意添字の完備基底上の有限正則性、通常商の完備性と指数1の評価を与える。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## RootRelationFiniteAmbient -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Andre DerivedCompletion RingTheory.Sequence
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)
variable {r : ℕ} (ι : Fin r → J)
local notation "Raw" => rootFamilyRaw p R J
local notation "Base" => rootFamilyBase p R J
local notation "Poly" => MvPolynomial J R

/-- 生の根付き基底上で選んだ初期変数の有限列。 -/
def rootRelationFiniteAmbientRawSequence : Fin r → Raw :=
  fun i => rootFamilyPolynomialMap p R J (MvPolynomial.X (R := R) (ι i))

/-- 実完備化した基底上の、選んだ初期変数の有限列。 -/
def rootRelationFiniteAmbientSequence : Fin r → Base :=
  rootFamilyUnit p R J ∘ rootRelationFiniteAmbientRawSequence p R J ι

/-- 生の有限関係の生成イデアルは、対応する変数部分族のイデアル。 -/
theorem rootRelationFiniteAmbientRawIdeal_eq :
    Ideal.span (Set.range (rootRelationFiniteAmbientRawSequence p R J ι)) =
      rootRelationSubsetRawIdeal p R J (Set.range ι) := by
  rw [rootRelationSubsetRawIdeal, polynomialSubsetIdeal, Ideal.map_span,
    ← Set.range_comp, ← Set.range_comp]
  rfl

/-- 任意添字の生の根付き環は、通常多項式環上で自由。 -/
theorem rootFamilyRaw_sparse_polynomial_free :
    letI := (rootFamilyPolynomialMap p R J).toAlgebra
    Module.Free Poly Raw := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  exact Module.Free.of_basis (rootFamilySparseFractionBasis p R J)

/-- 相異なる初期変数の像は、生の根付き基底上で弱正則。 -/
theorem rootRelationFiniteAmbientRaw_isWeaklyRegular (hι : Function.Injective ι) :
    RingTheory.Sequence.IsWeaklyRegular Raw
      (List.ofFn (rootRelationFiniteAmbientRawSequence p R J ι)) := by
  letI := (rootFamilyPolynomialMap p R J).toAlgebra
  letI := rootFamilyRaw_sparse_polynomial_free p R J
  have h : RingTheory.Sequence.IsWeaklyRegular Poly
      (List.ofFn (fun i => MvPolynomial.X (R := R) (ι i))) := by
    have h' := monicRelation_fin_isWeaklyRegular
      (fun _ : J => (Polynomial.X : Polynomial R))
      (fun _ => (Polynomial.monic_X : (Polynomial.X : Polynomial R).Monic)) ι hι
    simpa only [monicRelation, Polynomial.eval₂_X] using h'
  have ht : RingTheory.Sequence.IsWeaklyRegular (Poly ⊗[Poly] Raw)
      (List.ofFn (fun i => MvPolynomial.X (R := R) (ι i))) := h.isWeaklyRegular_rTensor
  have hb := ((TensorProduct.lid Poly Raw).isWeaklyRegular_congr
    (List.ofFn (fun i => MvPolynomial.X (R := R) (ι i)))).mp ht
  have hm := (isWeaklyRegular_map_algebraMap_iff (R := Poly) (S := Raw) Raw
    (List.ofFn (fun i => MvPolynomial.X (R := R) (ι i)))).mpr hb
  have he : algebraMap Poly Raw = rootFamilyPolynomialMap p R J := rfl
  rw [he] at hm
  change RingTheory.Sequence.IsWeaklyRegular Raw
    (List.ofFn (fun i => rootFamilyPolynomialMap p R J (MvPolynomial.X (R := R) (ι i))))
  simpa only [List.map_ofFn, Function.comp_def] using hm

/-- 生の基底上の有限初期変数は Koszul 分解を与える。 -/
theorem rootRelationFiniteAmbientRaw_isKoszulResolution (hι : Function.Injective ι) :
    SerrePositivity.IsKoszulResolution (rootRelationFiniteAmbientRawSequence p R J ι) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (rootRelationFiniteAmbientRaw_isWeaklyRegular p R J ι hι)

/-- 概要：任意添字の完備な根付き基底で、相異なる有限個の初期変数は Koszul 正則。
方針：生の環と有限関係商の自由性により、既存の各項完備化比較を使う。
規約：BS 著者版 Proposition 7.10。係数の p 正則性は不要。
使われ方：S′ の固定基底上の有限 lci 包絡。 -/
theorem rootRelationFiniteAmbient_isKoszulResolution (hι : Function.Injective ι) :
    SerrePositivity.IsKoszulResolution (rootRelationFiniteAmbientSequence p R J ι) := by
  letI : Module.Free R Raw := Module.Free.of_basis (AddMonoidAlgebra.basis _ _)
  let z := rootRelationFiniteAmbientRawSequence p R J ι
  letI : Module.Free R (Raw ⧸ Ideal.span (Set.range z)) := by
    rw [rootRelationFiniteAmbientRawIdeal_eq]
    exact Module.Free.of_basis (rootRelationSubsetRawBasis p R J (Set.range ι))
  exact completedKoszul_isKoszulResolution R Raw p z
    (rootRelationFiniteAmbientRaw_isKoszulResolution p R J ι hι)

/-- 完備な基底上の通常の有限初期関係商。 -/
abbrev rootRelationFiniteAmbientQuotient :=
  Base ⧸ (rootRelationSubsetRawIdeal p R J (Set.range ι)).map (rootFamilyUnit p R J)

/-- 通常の有限初期関係商は導来 p 完備。 -/
theorem rootRelationFiniteAmbientQuotient_complete :
    IsModuleComplete (rootRelationFiniteAmbientQuotient p R J ι)
      (p : rootRelationFiniteAmbientQuotient p R J ι)
      (ModuleCat.of _ (rootRelationFiniteAmbientQuotient p R J ι)) := by
  have hBase := principalCompletionRing_self_complete Raw p
  have h := isModuleComplete_finiteRelationQuotient Base (p : Base) hBase
    (rootRelationFiniteAmbientSequence p R J ι)
  have he : Ideal.span (Set.range (rootRelationFiniteAmbientSequence p R J ι)) =
      (rootRelationSubsetRawIdeal p R J (Set.range ι)).map (rootFamilyUnit p R J) := by
    rw [← rootRelationFiniteAmbientRawIdeal_eq, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [he] at h
  have h' := (isModuleComplete_algebraMap_iff Base
    (rootRelationFiniteAmbientQuotient p R J ι) (p : Base) _).mpr h
  simpa only [map_natCast] using h'

end SerrePositivity.BhattScholze.Semiperfectoid

end

/-! ## RootRelationFiniteAmbientBound -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Andre DerivedCompletion CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)
variable {r : ℕ} (ι : Fin r → J)

/-- 概要：有限初期関係の通常商のねじれは、有限族によらず p で消える。
方針：通常商は既に完備で、生の商の実完備化から指数1を同型で戻す。
規約：BS 著者版 Proposition 7.10。変数の相異性は完備性には不要。
使われ方：全有限部分族に共通の有界ねじれ評価。 -/
theorem rootRelationFiniteAmbientQuotient_torsion_bound_one (hR : IsIntegralPerfectoid R p)
    (n : ℕ) (x : rootRelationFiniteAmbientQuotient p R J ι)
    (hx : (p : rootRelationFiniteAmbientQuotient p R J ι) ^n * x = 0) :
    (p : rootRelationFiniteAmbientQuotient p R J ι) * x = 0 := by
  let Raw := rootFamilyRaw p R J
  let I := rootRelationSubsetRawIdeal p R J (Set.range ι)
  let S := rootRelationSubsetRaw p R J (Set.range ι)
  let T := rootRelationFiniteAmbientQuotient p R J ι
  obtain ⟨e₀, _⟩ := exists_principalCompletionQuotientEquiv_of_complete Raw p I
    (rootRelationFiniteAmbientQuotient_complete p R J ι)
  let e : T ≃+* CompletedRing p S := e₀
  letI := principalCompletionCommRing S (p : S)
  have hN : ∀ k : ℕ, ∀ y : S, (p : S) ^ k * y = 0 → (p : S) ^ 1 * y = 0 :=
    rootRelationSubsetRaw_torsion_bound p R J (Set.range ι) 1 (fun k y hy => by
      simpa only [pow_one] using hR.p_mul_eq_zero_of_pow_mul_eq_zero R p k y hy)
  have h := principalCompletionH0_uniform_torsion_bound S (p : S) 1 hN
  have hp : principalCompletionUnitRingHom S (p : S) (p : S) = (p : CompletedRing p S) :=
    map_natCast (principalCompletionUnitRingHom S (p : S)) p
  have hep : e (p : T) = (p : CompletedRing p S) := map_natCast e p
  apply e.injective
  have hx' : (p : CompletedRing p S) ^ n * e x = 0 := by
    simpa only [map_mul, map_pow, hep, map_zero] using congrArg e hx
  have h' := h n (e x) (by simpa only [hp] using hx')
  simpa only [hp, map_mul, hep, map_zero, pow_one] using h'

end SerrePositivity.BhattScholze.Semiperfectoid

end
