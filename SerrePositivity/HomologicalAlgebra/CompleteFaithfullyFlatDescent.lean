module
public import SerrePositivity.HomologicalAlgebra.DerivedKoszulDescent
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # 完備な導来対象のスカラーの零化の、完全忠実平坦な拡大に沿った降下

## 概要

`a` 進完備な導来対象のホモロジーの冪による零化を、Koszul の段のホモロジーの零化から得る（Milnor 列による比較）。二つの次数にだけコホモロジーを持つ完備な対象について、完全忠実平坦な拡大の後で錐のスカラーが零になれば元でも冪が零になることを示す。加群の写像の錐（上に有界な導来圏の対象 `moduleMapConeBoundedAbove`）について、スカラーの零化・同種性（`moduleMapConeIsogeny_descent`）とその単射版、有限自由加群への写像の同種性（`finiteFreeConeIsogeny_descent`）を拡大から元へ降ろす。

## 方針

Koszul の段と Milnor の標準塔を比べ、ホモロジーの零化を二段の対象の零化（HomologicalAlgebra/ScalarConeAnnihilators）へ渡す。

## 規約

拡大の存在は仮定として受け取る（どの拡大を取るかはここでは決めない）。後半は旧 `CLMST/IsogenyDescent`（CLMST Prop 2.4.7 の証明の降下の段 D1〜D6）。

## 使われ方

CLMST の `PerfectoidizationIsogeny`（Prop 2.4.7）の降下の背骨。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Compare actual Koszul homology with the standard representative tower used by Milnor. -/
def derivedKoszulStageHomologyEquiv (a : R) (X : DerivedCategory (ModuleCat.{u} R))
    (n : ℕ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X) ≃ₗ[R]
      (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X) n).homology i :=
  ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeFunctor R (a ^ n)).mapIso
          (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
        (derivedScalarConeComparison R (a ^ n)).app (DerivedCategory.Q.objPreimage X)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor (a ^ n)).obj (DerivedCategory.Q.objPreimage X))).toLinearEquiv

/-- Actual Koszul-stage annihilation passes through the standard complete Milnor comparison. -/
lemma completeDerived_homology_pow_annihilated_of_derivedKoszul (a : R)
    (X : DerivedCategory (ModuleCat.{u} R)) (hX : IsComplete R a X)
    (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n : ℕ,
      (∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X), g ^ N • x = 0) ∧
      (∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X), g ^ N • x = 0)) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X, g ^ (2 * N) • x = 0 := by
  apply completeDerived_homology_pow_annihilated R a X hX i g N
  intro n
  constructor
  · intro x
    let e := derivedKoszulStageHomologyEquiv R a X n i
    have hx := congrArg e ((h n).1 (e.symm x))
    simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply] using hx
  · intro x
    let e := derivedKoszulStageHomologyEquiv R a X n (i - 1)
    have hx := congrArg e ((h n).2 (e.symm x))
    simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply] using hx

/-- Scalar-cone reduction is linear on the actual derived category. -/
instance derivedScalarConeFunctor_linear (a : R) :
    (derivedScalarConeFunctor R a).Linear R := by
  let : Localization.Lifting
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (scalarConeFunctor a ⋙ DerivedCategory.Q) (derivedScalarConeFunctor R a) :=
    ⟨derivedScalarConeComparison R a⟩
  exact (Localization.functor_linear_iff
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) R
    (scalarConeFunctor a ⋙ DerivedCategory.Q) (derivedScalarConeFunctor R a)).mp inferInstance

/-- A derived scalar zero map gives the same annihilator on all scalar-cone homology. -/
lemma derivedScalarCone_homology_annihilated_of_scalar_eq_zero (a : R)
    (X : DerivedCategory (ModuleCat.{u} R)) (r : R) (hX : r • 𝟙 X = 0) (i : ℤ) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X), r • x = 0 := by
  have hz : (derivedScalarConeFunctor R a).map (0 : X ⟶ X) = 0 := by
    simpa only [zero_smul] using (derivedScalarConeFunctor R a).map_smul (0 : R) (𝟙 X)
  have h := congrArg ((derivedScalarConeFunctor R a).map) hX
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, hz] at h
  have hH := congrArg ((DerivedCategory.homologyFunctor (ModuleCat R) i).map) h
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at hH
  intro x
  exact congrArg (fun f => f.hom x) hH

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- A uniform power-Koszul annihilator after completely faithful flat extension descends. -/
lemma complete_two_cohomology_scalar_pow_eq_zero_of_completelyFaithfullyFlat
    (a : R) (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (hX : IsComplete R a X.obj)
    (lo hi : ℤ) (hlohi : lo + 1 = hi) [X.obj.IsGE lo] [X.obj.IsLE hi] (g : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ i ∈ ({lo, lo - 1, hi, hi - 1} : Set ℤ),
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj X)).obj, (φ g) ^ N • x = 0) :
    g ^ (4 * N) • 𝟙 X.obj = 0 := by
  have hR : ∀ n : ℕ, ∀ i ∈ ({lo, lo - 1, hi, hi - 1} : Set ℤ),
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X.obj), g ^ N • x = 0 := by
    intro n i hi
    apply (derivedKoszulHomology_annihilated_iff φ a hS n X (g ^ N) i).mp
    simpa only [map_pow] using h n i hi
  have hLo := completeDerived_homology_pow_annihilated_of_derivedKoszul R a X.obj hX lo g N
    (fun n => ⟨hR n lo (by simp), hR n (lo - 1) (by simp)⟩)
  have hHi := completeDerived_homology_pow_annihilated_of_derivedKoszul R a X.obj hX hi g N
    (fun n => ⟨hR n hi (by simp), hR n (hi - 1) (by simp)⟩)
  have hz := two_cohomology_scalar_pow_eq_zero R X.obj lo hi hlohi g (2 * N) hLo hHi
  simpa only [← Nat.mul_assoc] using hz

end SerrePositivity

section IsogenyDescentPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The actual cone of a module morphism as a bounded-above derived object. -/
def moduleMapConeBoundedAbove (f : M →ₗ[R] N) : DerivedCategory.Minus (ModuleCat.{u} R) :=
  ⟨moduleMapCone R f, ⟨0, by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsLE 0
    infer_instance⟩⟩

/-- Uniform annihilation in the three relevant degrees after extension gives a scalar zero cone. -/
theorem moduleMapConeScalar_descent (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R) (q : ℕ)
    (h : ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0) :
    moduleMapConeScalar R f (g ^ (4 * q)) = 0 := by
  let X := moduleMapConeBoundedAbove f
  have : X.obj.IsGE (-1) := by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsGE (-1)
    infer_instance
  have : X.obj.IsLE 0 := by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsLE 0
    infer_instance
  apply complete_two_cohomology_scalar_pow_eq_zero_of_completelyFaithfullyFlat
    φ a hS X hC (-1) 0 (by decide) g q
  intro n i hi
  apply h n i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with hi | hi | hi | hi <;> subst i <;> norm_num

/-- Isogeny descent with a specified extension and a uniform annihilator. -/
theorem moduleMapConeIsogeny_descent (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R)
    (h : ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f (g ^ q) = 0 ∧
      (∀ x : f.ker, g ^ q • x = 0) ∧ (∀ x : N ⧸ f.range, g ^ q • x = 0) := by
  obtain ⟨q, hq⟩ := h
  have hz := moduleMapConeScalar_descent φ a hS f hC g q hq
  exact ⟨4 * q, hz, moduleMapCone_pow_scalar_eq_zero_annihilates R f g (4 * q) hz⟩

/-- If g acts regularly on the source, the descended isogeny is injective. -/
theorem moduleMapConeIsogeny_descent_injective (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R)
    (hg : IsSMulRegular M g)
    (h : ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0) :
    Function.Injective f ∧ ∃ q : ℕ, ∀ x : N ⧸ f.range, g ^ q • x = 0 := by
  obtain ⟨q, hq, _, _⟩ := moduleMapConeIsogeny_descent φ a hS f hC g h
  obtain ⟨hf, hc⟩ := moduleMapCone_pow_scalar_eq_zero_injective_of_regular R f g q hg hq
  exact ⟨hf, q, hc⟩

/-- E5 supplies the uniform exponent if the extended reductions compare to a finite-free cone. -/
theorem finiteFreeConeIsogeny_descent [IsReduced S]
    (a : R) (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R)
    {L : Type u} [AddCommGroup L] [Module S L] [Module.Finite S L]
    (r : ℕ) (u : L →ₗ[S] (Fin r → S))
    (hu : Function.Bijective (awayModuleMap (φ g) u))
    (comparison : ∀ n : ℕ,
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj ≅
      (derivedScalarConeFunctor S ((φ a) ^ n)).obj (moduleMapCone S u)) :
    ∃ q : ℕ, moduleMapConeScalar R f (g ^ q) = 0 ∧
      (∀ x : f.ker, g ^ q • x = 0) ∧ (∀ x : N ⧸ f.range, g ^ q • x = 0) := by
  obtain ⟨q, hq⟩ := finiteFreeConeIsogeny S (φ g) r u hu
  apply moduleMapConeIsogeny_descent φ a hS f hC g
  refine ⟨q, fun n i hi x => ?_⟩
  let e := (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso (comparison n)
  have hc := derivedScalarCone_homology_annihilated_of_scalar_eq_zero S
    ((φ a) ^ n) (moduleMapCone S u) ((φ g) ^ q) hq i
  apply e.toLinearEquiv.injective
  simp only [map_smul, map_zero]
  exact hc (e.hom x)

end SerrePositivity

end IsogenyDescentPart
