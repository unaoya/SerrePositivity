module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Discrete
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 主元完備化の共通指数と全射性

## 概要
指定したねじれ指数を実完備化と完全平坦代数へ渡し、前完備な環の単位の全射性を得る。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## CompleteFlatUniformBound -/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))

/-- 概要：離散平坦な還元を持つ完備対象の H⁰ は、係数環と同じ指定指数を持つ。
方針：Koszul 塔のねじれの関係式を逆極限へ渡す。
規約：BS 著者版 Proposition 7.10 の一様性。正則性は不要。
使われ方：有限関係の長さに依らない完備化の評価。 -/
theorem completeFlatReduction_uniform_torsion_bound
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hc : IsComplete R a X.obj) (N : ℕ)
    (hN : ∀ n : ℕ, ∀ x : R, a ^ n * x = 0 → a ^ N * x = 0)
    (n : ℕ) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj)
    (hx : a ^ n • x = 0) : a ^ N • x = 0 := by
  let M : ℕ → Type u := fun k =>
    (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex k).homology 0
  let t := fun k => (homologyMap
    (powerCokernelComplexTransition a (boundedAboveDerivedChosenModel X).complex k) 0).hom
  have hLim := moduleTowerLimit_power_torsion_bound_of_relations a N M t
    (powerCokernelH0_power_annihilated a X)
    (powerCokernelH0_torsion_relation a X hPure hFlat N hN)
  let e := (completeFlatReductionH0LimitIso a X hPure hFlat ⟨N, hN⟩ hc).toLinearEquiv
  apply e.injective
  rw [map_smul, map_zero]
  apply hLim n (e x)
  rw [← map_smul, hx, map_zero]

end SerrePositivity.DerivedCompletion

end

/-! ## PrincipalCompletionUniformBound -/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open BhattScholze.Andre.Transfinite
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (a : R)

/-- 概要：係数環の指定指数 N は実 H⁰ 完備化のねじれも消す。
方針：実導来完備化の還元を自由な剰余環へ比較し、逆極限で指数を保存する。
規約：BS 著者版 Proposition 7.10。a 正則性も非零性も不要。
使われ方：根関係商の一様ねじれと生の余極限の完備化。 -/
theorem principalCompletionH0_uniform_torsion_bound (N : ℕ)
    (hN : ∀ n : ℕ, ∀ x : R, a ^ n * x = 0 → a ^ N * x = 0) :
    letI := principalCompletionCommRing R a
    ∀ n : ℕ, ∀ x : PrincipalCompletionH0 R a,
      (principalCompletionUnitRingHom R a a) ^ n * x = 0 →
        (principalCompletionUnitRingHom R a a) ^ N * x = 0 := by
  letI := principalCompletionCommRing R a
  let X0 := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)
  let X := (boundedAboveDerivedCompletionFunctor R a).obj X0
  let q := Ideal.Quotient.mk (Ideal.span {a})
  let e0 := completedUnitReductionIso R a
  have hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) := by
    intro i hi
    exact (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).mapIso
        (DerivedCategory.Minus.ι.mapIso e0))
  have hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) := by
    let e := (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso e0) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (R ⧸ Ideal.span {a})) 0).app _
    letI := q.toAlgebra
    have hf : Module.Flat (R ⧸ Ideal.span {a})
        ((ModuleCat.extendScalars q).obj (ModuleCat.of R R)) :=
      Module.Flat.of_linearEquiv
        (TensorProduct.AlgebraTensorModule.rid R (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}))
    exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr hf
  let e := (principalCompletedUnitH0Iso R a).toLinearEquiv
  change ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj) ≃ₗ[R]
    PrincipalCompletionH0 R a at e
  have he (k : ℕ) (x : PrincipalCompletionH0 R a) :
      (principalCompletionUnitRingHom R a a) ^k * x = a^k • x := by
    rw [← map_pow]
    exact (principalCompletionH0_isCompleteModuleReflection R a).mul_scalar_unit _ x
  intro n x hx
  rw [he] at hx ⊢
  apply e.symm.injective
  rw [map_smul, map_zero]
  apply completeFlatReduction_uniform_torsion_bound a X hPure hFlat
    (derivedComplexCompletionFunctor_isComplete R a X0.obj) N hN n
  simpa only [map_smul, map_zero] using congrArg e.symm hx

end SerrePositivity.DerivedCompletion

end

/-! ## CompletelyFlatUniformBound -/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：p 完備な完全平坦代数へ係数環の同じねじれ指数を移す。
方針：single 模型の離散平坦還元と共通指数を逆極限に渡す。
規約：BS 著者版 Proposition 7.10。完全忠実性を使わない一般化。
使われ方：有限部分族包絡の剰余の一様ねじれ。 -/
theorem completelyFlat_uniform_torsion_bound (p : ℕ) (f : R →+* S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : letI := f.toAlgebra; IsCompletelyFlat (Ideal.span {(p : R)}) S)
    (N : ℕ) (hN : ∀ n : ℕ, ∀ x : R, (p : R) ^n * x = 0 → (p : R) ^N * x = 0)
    (n : ℕ) (x : S) (hx : (p : S) ^n * x = 0) : (p : S) ^N * x = 0 := by
  letI := f.toAlgebra
  let M := ModuleCat.of R S
  let X := boundedAboveDerivedSingleFunctor.obj M
  have hD := BhattScholze.Prismatic.discrete_completelyFlat (Ideal.span {(p : R)}) M hflat
  have hc : IsComplete R (p : R) X.obj := by
    apply (isModuleComplete_algebraMap_iff R S (p : R) S).mp
    simpa only [map_natCast] using hS
  let e := ((realizedSingleH0Iso R).app M).toLinearEquiv
  have he (k : ℕ) (y : S) : (p : S) ^k * y = (p : R) ^k • y := by
    simp only [Algebra.smul_def, map_pow, map_natCast]
  rw [he] at hx ⊢
  apply e.symm.injective
  rw [map_smul, map_zero]
  apply completeFlatReduction_uniform_torsion_bound (p : R) X hD.1 hD.2 hc N hN n
  simpa only [map_smul, map_zero] using congrArg e.symm hx

end SerrePositivity.DerivedCompletion

end

/-! ## PrincipalCompletionSurjective -/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (a : R)

/-- 概要：前完備かつ有界ねじれの環の、実主元完備化への単位は全射。
方針：古典的完備化の単位の全射性を、単位を保つ代数同型で戻す。
規約：BS 著者版 Proposition 7.10。通常環と完備化の同型は主張しない。
使われ方：S′ への商射と Corollary 7.3 の全射入力。 -/
theorem principalCompletionUnit_surjective_of_precomplete
    [IsPrecomplete (Ideal.span {a}) R]
    (hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R, a^n * x = 0 → a^N * x = 0) :
    letI := principalCompletionCommRing R a
    Function.Surjective (principalCompletionUnitRingHom R a) := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let e := boundedPrincipalCompletionAdicAlgEquiv R a hbound
  intro x
  obtain ⟨r, hr⟩ := AdicCompletion.of_surjective (Ideal.span {a}) R (e x)
  refine ⟨r, e.injective ?_⟩
  exact (e.commutes r).trans hr

end SerrePositivity.DerivedCompletion

end
