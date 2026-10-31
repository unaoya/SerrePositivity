module

public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Graded
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.ReesPresentation
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import Mathlib.Data.Int.Interval
public import SerrePositivity.HomologicalAlgebra.AdicFilteredComplex

/-! # Rees 環を経由した Koszul 複体の adic な非輪状性

## 概要

Koszul 複体を Rees 環上で評価し、次数付き Koszul ホモロジーの消滅から、元の Koszul 複体の `I` 進の尾部が
十分先で非輪状であること（`eventually_adicTail_acyclic`）を示す。

## 方針

次数付きの完全性を adic フィルトレーションの完全性へ移す一般論（`GradedAdicExactness`）を Koszul 複体に
適用する。

## 規約

名前空間は `KoszulMultiplicity`。

## 使われ方

Koszul 重複度の公式（`KoszulMultiplicity/Formula`）。
-/

@[expose] public noncomputable section

universe u v w

section Evaluation

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory HilbertSamuel Polynomial

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- Rees 代数の t = 1 における評価。 -/
def reesEvalOne : reesAlgebra I →ₐ[R] R :=
  (Polynomial.aeval (1 : R)).comp (reesAlgebra I).val

/-- Rees 加群を係数環の加群として見た t = 1 評価。 -/
def evaluationR : ReesModule R I R →ₗ[R] R :=
  (reesEvalOne R I).toLinearMap.comp ((reesModuleSelfEquiv R I).toLinearMap.restrictScalars R)

/-- X_i を z_i t に送ってから t = 1 で評価すると、X_i ↦ z_i の評価になる。 -/
theorem reesEvalOne_comp_presentation {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) :
    (reesEvalOne R I).comp (reesPresentation R I z hz) = MvPolynomial.aeval z := by
  ext i
  simp [reesEvalOne, reesPresentation]

/-- 多項式環が X_i ↦ z_i によって係数環自身に作用する。 -/
@[instance_reducible]
def evaluatedModule {h : ℕ} (z : Fin h → R) : Module (MvPolynomial (Fin h) R) R :=
  Module.compHom R (MvPolynomial.aeval z).toRingHom

/-- Rees 加群の評価は、両側を対応する評価による多項式加群として見ると線形である。 -/
def evaluation {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    let _ := HilbertSamuel.reesPolynomialModule I (HilbertSamuel.ReesModule R I R) z hz
    let _ := evaluatedModule R z
    ReesModule R I R →ₗ[MvPolynomial (Fin h) R] R := by
  let := HilbertSamuel.reesPolynomialModule I (HilbertSamuel.ReesModule R I R) z hz
  let := evaluatedModule R z
  refine {
    toFun := evaluationR R I
    map_add' := (evaluationR R I).map_add
    map_smul' := ?_ }
  intro p m
  change reesEvalOne R I (reesModuleSelfEquiv R I ((reesPresentation R I z hz p) • m)) =
    MvPolynomial.aeval z p * reesEvalOne R I (reesModuleSelfEquiv R I m)
  rw [(reesModuleSelfEquiv R I).map_smul]
  change reesEvalOne R I ((reesPresentation R I z hz p) * reesModuleSelfEquiv R I m) = _
  rw [map_mul]
  have h := DFunLike.congr_fun (reesEvalOne_comp_presentation R I z hz) p
  change reesEvalOne R I (reesPresentation R I z hz p) = MvPolynomial.aeval z p at h
  rw [h]

/-- 多項式環上の係数対象としての Rees 加群。 -/
def sourceModule {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    ModuleCat.{u} (MvPolynomial (Fin h) R) :=
  let _ := HilbertSamuel.reesPolynomialModule I (HilbertSamuel.ReesModule R I R) z hz
  ModuleCat.of _ (ReesModule R I R)

/-- 係数環を X_i ↦ z_i に沿って係数制限した、多項式環上の対象。 -/
def targetModule {h : ℕ} (z : Fin h → R) : ModuleCat.{u} (MvPolynomial (Fin h) R) :=
  (ModuleCat.restrictScalars (MvPolynomial.aeval z).toRingHom).obj (ModuleCat.of R R)

/-- 多項式加群としての t = 1 評価射。 -/
def evaluationHom {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    sourceModule R I z hz ⟶ targetModule R z := by
  let := HilbertSamuel.reesPolynomialModule I (HilbertSamuel.ReesModule R I R) z hz
  let := evaluatedModule R z
  exact ModuleCat.ofHom (evaluation R I z hz)

/-- 多項式作用を係数環へ制限しても、元の Rees 加群の係数作用に戻る。 -/
def sourceCoefficientEquiv {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) :
    (ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj
      (sourceModule R I z hz) ≃ₗ[R] ReesModule R I R := by
  let := HilbertSamuel.reesPolynomialModule I (HilbertSamuel.ReesModule R I R) z hz
  refine {
    toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := ?_ }
  intro r m
  change reesPresentation R I z hz (algebraMap R (MvPolynomial (Fin h) R) r) •
    (show ReesModule R I R from m) = r • (show ReesModule R I R from m)
  rw [(reesPresentation R I z hz).commutes]
  exact algebraMap_smul (reesAlgebra I) r (show ReesModule R I R from m)

/-- 評価された係数環を係数へ制限すると、元の係数環自身に戻る。 -/
def targetCoefficientEquiv {h : ℕ} (z : Fin h → R) :
    (ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj
      (targetModule R z) ≃ₗ[R] R := by
  refine {
    toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := ?_ }
  intro r m
  change MvPolynomial.aeval z (algebraMap R (MvPolynomial (Fin h) R) r) *
    (show R from m) = r * (show R from m)
  rw [(MvPolynomial.aeval z).commutes]
  rfl

/-- Rees 係数次数を、多項式環からの係数制限で得る R 加群へ移す。 -/
def sourceCoefficientGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (n : ℕ) :
    Submodule R ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj
      (sourceModule R I z hz)) :=
  ((reesSingle R I R n).range).map (sourceCoefficientEquiv R I z hz).symm.toLinearMap

/-- 係数制限へ移送した Rees の係数次数は内部直和分解をなす。 -/
theorem isInternal_sourceCoefficientGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) :
    DirectSum.IsInternal (sourceCoefficientGrade R I z hz) := by
  let : DirectSum.Decomposition (GradedKoszul.reesModuleGrade R I R) :=
    (GradedKoszul.isInternal_reesModuleGrade R I R).chooseDecomposition
  exact GradedKoszul.isInternal_map_equiv (GradedKoszul.reesModuleGrade R I R)
    (sourceCoefficientEquiv R I z hz).symm

/-- 各変数の作用は、Rees の係数次数を一つ上げる。 -/
theorem sourceCoefficientGrade_variables_degree {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) :
    ∀ (j : Fin h) (n : ℕ), ∀ m ∈ sourceCoefficientGrade R I z hz n,
      GradedKoszul.scalarOnModule (MvPolynomial.X j) (sourceModule R I z hz) m ∈
        sourceCoefficientGrade R I z hz (n + 1) := by
  intro j n m hm
  obtain ⟨a, ha, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := ha
  let t : I := ⟨z j, hz ▸ Ideal.subset_span (Set.mem_range_self j)⟩
  refine ⟨reesSingle R I R (n + 1) (adicMultiplication R I R t n b), ⟨_, rfl⟩, ?_⟩
  apply (sourceCoefficientEquiv R I z hz).injective
  change reesSingle R I R (n + 1) (adicMultiplication R I R t n b) =
    reesPresentation R I z hz (MvPolynomial.X j) • reesSingle R I R n b
  have hp : reesPresentation R I z hz (MvPolynomial.X j) = reesDegreeOne R I t := by
    apply Subtype.ext
    exact reesPresentation_X R I z hz j
  rw [hp, reesDegreeOne_smul_reesSingle]

/-- Rees 係数加群の変数列による Koszul 複体。 -/
def sourceComplex {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    CochainComplex (ModuleCat.{u} (MvPolynomial (Fin h) R)) ℤ :=
  (koszulModuleFunctor MvPolynomial.X).obj (sourceModule R I z hz)

/-- 変数の評価像は、元の生成列である。 -/
theorem eval_variables {h : ℕ} (z : Fin h → R) :
    (MvPolynomial.aeval z).toRingHom ∘ (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) = z := by
  funext i
  exact MvPolynomial.aeval_X z i

/-- 評価係数での Koszul 構成と、元の Koszul 複体の多項式環への係数制限との同型。 -/
def targetComplexIso {h : ℕ} (z : Fin h → R) :
    (koszulModuleFunctor MvPolynomial.X).obj (targetModule R z) ≅
      ((ModuleCat.restrictScalars (MvPolynomial.aeval z).toRingHom).mapHomologicalComplex
        (.up ℤ)).obj (koszulComplex z) := by
  have e := koszulModuleRestrictIso (MvPolynomial.aeval z).toRingHom
    (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R)
  rw [eval_variables R z] at e
  exact e

/-- 評価により、Rees Koszul 複体から元の Koszul 複体へ多項式環上の複体射ができる。 -/
def evaluationChainMap {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    sourceComplex R I z hz ⟶
      ((ModuleCat.restrictScalars (MvPolynomial.aeval z).toRingHom).mapHomologicalComplex
        (.up ℤ)).obj (koszulComplex z) :=
  (koszulModuleFunctor MvPolynomial.X).map (evaluationHom R I z hz) ≫ (targetComplexIso R z).hom

/-- 多項式の評価と係数の包含を合成すると係数環の恒等写像になる。 -/
theorem evaluation_comp_algebraMap {h : ℕ} (z : Fin h → R) :
    RingHom.id R = (MvPolynomial.aeval z).toRingHom.comp
      (algebraMap R (MvPolynomial (Fin h) R)) := by
  ext r
  exact ((MvPolynomial.aeval z).commutes r).symm

/-- 二段の係数制限を、元の係数環上の Koszul 複体へ戻す同型。 -/
def doubleRestrictionIso {h : ℕ} (z : Fin h → R) :
    ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).mapHomologicalComplex
      (.up ℤ)).obj
        (((ModuleCat.restrictScalars (MvPolynomial.aeval z).toRingHom).mapHomologicalComplex
          (.up ℤ)).obj (koszulComplex z)) ≅ koszulComplex z := by
  let e := (ModuleCat.restrictScalarsComp'
    (algebraMap R (MvPolynomial (Fin h) R)) (MvPolynomial.aeval z).toRingHom
    (RingHom.id R) (evaluation_comp_algebraMap R z)).symm ≪≫ ModuleCat.restrictScalarsId R
  exact (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app (koszulComplex z) ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (.up ℤ)).app (koszulComplex z)

/-- Rees Koszul 複体から、係数環上の元の Koszul 複体への複体射。 -/
def evaluationChainMapR {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).mapHomologicalComplex
      (.up ℤ)).obj (sourceComplex R I z hz) ⟶ koszulComplex z :=
  ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).mapHomologicalComplex
    (.up ℤ)).map (evaluationChainMap R I z hz) ≫ (doubleRestrictionIso R z).hom

/-- 係数次数 n の単項式の評価は、その係数そのものである。 -/
@[simp]
theorem evaluationR_reesSingle (n : ℕ) (x : adicSubmodule R I R n) :
    evaluationR R I (reesSingle R I R n x) = (x : R) := by
  change (Polynomial.aeval (1 : R)) (reesModuleSelfEquiv R I (reesSingle R I R n x) : R[X]) = _
  rw [reesModuleSelfEquiv_reesSingle]
  simp [Polynomial.aeval_def]

theorem reesSingle_injective (n : ℕ) : Function.Injective (reesSingle R I R n) := by
  intro x y h
  have he := congrArg (reesCoefficient R I R n) h
  simpa only [reesCoefficient_reesSingle] using he

/-- 各係数次数で、t = 1 評価は I^n 上への線形同型である。 -/
def coefficientGradeEquiv (n : ℕ) :
    (reesSingle R I R n).range ≃ₗ[R] adicSubmodule R I R n :=
  (LinearEquiv.ofInjective (reesSingle R I R n) (reesSingle_injective R I n)).symm

/-- 上の同型の underlying map は評価そのものである。 -/
theorem coefficientGradeEquiv_coe (n : ℕ) (x : (reesSingle R I R n).range) :
    ((coefficientGradeEquiv R I n x : adicSubmodule R I R n) : R) = evaluationR R I x := by
  calc
    _ = evaluationR R I (reesSingle R I R n (coefficientGradeEquiv R I n x)) :=
      (evaluationR_reesSingle R I n _).symm
    _ = _ := congrArg (evaluationR R I) (congrArg Subtype.val
      ((LinearEquiv.ofInjective (reesSingle R I R n)
        (reesSingle_injective R I n)).apply_symm_apply x))

/-- 係数次数 n の全体の像は、ちょうど I^n である。 -/
theorem evaluationR_map_coefficientGrade (n : ℕ) :
    ((reesSingle R I R n).range).map (evaluationR R I) = adicSubmodule R I R n := by
  rw [← LinearMap.range_comp]
  have heq : (evaluationR R I).comp (reesSingle R I R n) =
      (adicSubmodule R I R n).subtype := by
    ext x
    exact evaluationR_reesSingle R I n x
  rw [heq, Submodule.range_subtype]

/-- 係数次数を固定すれば評価は単射である。 -/
theorem evaluationR_injective_coefficientGrade (n : ℕ) :
    Function.Injective ((evaluationR R I).domRestrict (reesSingle R I R n).range) := by
  intro x y hxy
  apply (coefficientGradeEquiv R I n).injective
  apply Subtype.ext
  change evaluationR R I x = evaluationR R I y at hxy
  simpa only [coefficientGradeEquiv_coe] using hxy

theorem coefficient_evaluation_conjugation {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) :
    (targetCoefficientEquiv R z).toLinearMap.comp
      (((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).map
        (evaluationHom R I z hz)).hom.comp (sourceCoefficientEquiv R I z hz).symm.toLinearMap) =
      evaluationR R I := by
  ext m
  rfl

/-- 係数制限で移送した次数成分の評価像は、対応するイデアル冪の全体である。 -/
theorem map_sourceCoefficientGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (n : ℕ) :
    (sourceCoefficientGrade R I z hz n).map
      ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).map
        (evaluationHom R I z hz)).hom = I ^ n • ⊤ := by
  apply Submodule.map_injective_of_injective (targetCoefficientEquiv R z).injective
  rw [sourceCoefficientGrade, ← Submodule.map_comp, ← Submodule.map_comp,
    LinearMap.comp_assoc, coefficient_evaluation_conjugation,
    Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (targetCoefficientEquiv R z).surjective]
  exact evaluationR_map_coefficientGrade R I n

/-- 係数制限で移送した各次数成分上で評価は単射である。 -/
theorem injOn_sourceCoefficientGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (n : ℕ) :
    Set.InjOn
      ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).map
        (evaluationHom R I z hz)).hom (sourceCoefficientGrade R I z hz n) := by
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hvalue := congrArg (targetCoefficientEquiv R z) hab
  change evaluationR R I a' = evaluationR R I b' at hvalue
  have hvalue' : ((evaluationR R I).domRestrict (reesSingle R I R n).range) ⟨a', ha'⟩ =
      ((evaluationR R I).domRestrict (reesSingle R I R n).range) ⟨b', hb'⟩ := hvalue
  have hsub := evaluationR_injective_coefficientGrade R I n hvalue'
  exact congrArg (sourceCoefficientEquiv R I z hz).symm (congrArg Subtype.val hsub)

/-- 元の Koszul 複体へ戻す R 上の同型。 -/
def targetComplexIsoR {h : ℕ} (z : Fin h → R) :
    GradedKoszul.underlyingComplex (R := R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (targetModule R z) ≅ koszulComplex z :=
  ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).mapHomologicalComplex
    (.up ℤ)).mapIso (targetComplexIso R z) ≪≫ doubleRestrictionIso R z

/-- 元の Koszul 複体へ戻す各項の R 線形同型。 -/
def targetTermEquiv {h : ℕ} (z : Fin h → R) (q : ℤ) :
    (GradedKoszul.underlyingComplex (R := R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (targetModule R z)).X q ≃ₗ[R]
        (koszulComplex z).X q :=
  ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) q).mapIso
    (targetComplexIsoR R z)).toLinearEquiv

/-- Rees Koszul 複体の各項の係数次数成分。 -/
def sourceTermGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (q : ℤ) (n : ℕ) :
    Submodule R
      ((GradedKoszul.underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X q) :=
  GradedKoszul.termGrade MvPolynomial.X (sourceModule R I z hz)
    (sourceCoefficientGrade R I z hz) q n

theorem evaluationChainMapR_term {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (q : ℤ) :
    ((evaluationChainMapR R I z hz).f q).hom =
      (targetTermEquiv R z q).toLinearMap.comp
        (KoszulMultiplicity.termMap MvPolynomial.X (evaluationHom R I z hz) q) := by
  ext m
  rfl

/-- 各 Koszul 項の係数次数 n の評価像は、その項の I^n 倍に一致する。 -/
theorem map_sourceTermGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (q : ℤ) (n : ℕ) :
    (sourceTermGrade R I z hz q n).map ((evaluationChainMapR R I z hz).f q).hom =
      (I ^ n • ⊤ : Submodule R ((koszulComplex z).X q)) := by
  rw [evaluationChainMapR_term, Submodule.map_comp]
  have hm := KoszulMultiplicity.map_termGrade MvPolynomial.X (evaluationHom R I z hz)
    (sourceCoefficientGrade R I z hz) (fun n ↦ I ^ n • ⊤)
    (map_sourceCoefficientGrade R I z hz) q n
  rw [sourceTermGrade, hm, KoszulMultiplicity.termGrade_ideal_smul_top,
    Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (targetTermEquiv R z q).surjective]

/-- 各 Koszul 項の係数次数成分に制限した評価は単射である。 -/
theorem injOn_sourceTermGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (q : ℤ) (n : ℕ) :
    Set.InjOn ((evaluationChainMapR R I z hz).f q).hom
      {a | a ∈ sourceTermGrade R I z hz q n} := by
  intro a ha b hb hab
  rw [evaluationChainMapR_term] at hab
  exact KoszulMultiplicity.injOn_termGrade MvPolynomial.X (evaluationHom R I z hz)
    (sourceCoefficientGrade R I z hz) (injOn_sourceCoefficientGrade R I z hz) q n
    ha hb ((targetTermEquiv R z q).injective hab)

end SerrePositivity.KoszulMultiplicity

end Evaluation

section Vanishing

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory GradedKoszul

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)

/-- The Rees differential raises coefficient degree by one. -/
theorem sourceTermGrade_differential (q : ℤ) (k : ℕ)
    (y : (underlyingComplex (R := R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X q)
    (hy : y ∈ sourceTermGrade R I z hz q k) :
    ((underlyingComplex (R := R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).d
        q (q + 1)).hom y ∈ sourceTermGrade R I z hz (q + 1) (k + 1) :=
  differential_mem_termGrade MvPolynomial.X (sourceModule R I z hz)
    (sourceCoefficientGrade R I z hz)
    (sourceCoefficientGrade_variables_degree R I z hz) q k y hy

/-- In all sufficiently large coefficient degrees, homogeneous cycles in
the Rees Koszul complex have homogeneous primitives one degree lower. -/
theorem exists_uniform_bound_source_boundary [IsNoetherianRing R] :
    ∃ b : ℕ, 0 < b ∧ ∀ q : ℤ, ∀ k ≥ b,
      ∀ y : (underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X q,
      y ∈ sourceTermGrade R I z hz q k →
      ((underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).d
          q (q + 1)).hom y = 0 →
      ∃ a : (underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X (q - 1),
        a ∈ sourceTermGrade R I z hz (q - 1) (k - 1) ∧
          ((underlyingComplex (R := R)
            (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).d
              (q - 1) q).hom a = y := by
  let : Module.Finite (MvPolynomial (Fin h) R) (sourceModule R I z hz) := by
    dsimp only [sourceModule]
    exact HilbertSamuel.reesPolynomialModule_finite I (HilbertSamuel.ReesModule R I R) z hz
  let : DirectSum.Decomposition (sourceCoefficientGrade R I z hz) :=
    (isInternal_sourceCoefficientGrade R I z hz).chooseDecomposition
  exact exists_uniform_bound_polynomialKoszul_boundary h (sourceModule R I z hz)
    (sourceCoefficientGrade R I z hz) (sourceCoefficientGrade_variables_degree R I z hz)

end SerrePositivity.KoszulMultiplicity

end Vanishing

section AdicExactness

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable {C P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (NS : ∀ q : ℤ, ℕ → Submodule R (C.X q)) (E : C ⟶ P) (I : Ideal R)
variable (himage : ∀ q k, (NS q k).map (E.f q).hom = I ^ k • ⊤)
variable (hinj : ∀ q k, Set.InjOn (E.f q).hom (NS q k))
variable (hdegree : ∀ q k, ∀ m ∈ NS q k,
  C.d q (q + 1) m ∈ NS (q + 1) (k + 1))

/-- Evaluation commutes with the differential. -/
theorem differential_eval (q r : ℤ) (m : C.X q) :
    P.d q r (E.f q m) = E.f r (C.d q r m) :=
  congrArg (fun f => f m) (E.comm q r)

include himage hdegree in
/-- The degree-zero image is the whole target term, and the differential raises
source degree, so the evaluated differential has entries in `I`. -/
theorem differential_range_le : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤ := by
  intro q
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ (NS q 0).map (E.f q).hom := by rw [himage]; simp
  obtain ⟨m, hm, hem⟩ := Submodule.mem_map.mp hx
  have hdm : E.f (q + 1) (C.d q (q + 1) m) ∈ I • (⊤ : Submodule R (P.X (q + 1))) := by
    have h : E.f (q + 1) (C.d q (q + 1) m) ∈
        (NS (q + 1) 1).map (E.f (q + 1)).hom :=
      Submodule.mem_map.mpr ⟨C.d q (q + 1) m, hdegree q 0 m hm, rfl⟩
    rw [himage, pow_one] at h
    exact h
  have hcomm := differential_eval E q (q + 1) m
  rw [hem] at hcomm
  rw [hcomm]
  exact hdm

include himage hinj hdegree in
/-- A closed element of a target adic power lifts to a closed source component. -/
theorem exists_closed_lift (q : ℤ) (k : ℕ) (x : P.X q)
    (hx : x ∈ I ^ k • (⊤ : Submodule R (P.X q))) (hdx : P.d q (q + 1) x = 0) :
    ∃ m : C.X q, m ∈ NS q k ∧ E.f q m = x ∧ C.d q (q + 1) m = 0 := by
  rw [← himage q k] at hx
  obtain ⟨m, hm, hem⟩ := Submodule.mem_map.mp hx
  refine ⟨m, hm, hem, ?_⟩
  apply hinj (q + 1) (k + 1) (hdegree q k m hm) (Submodule.zero_mem _)
  have hcomm := differential_eval E q (q + 1) m
  rw [hem, hdx] at hcomm
  exact hcomm.symm.trans ((E.f (q + 1)).hom.map_zero.symm)

include himage hinj hdegree in
/-- A boundary lift in the graded source becomes a boundary with one lower adic power. -/
theorem exists_adic_boundary (q : ℤ) (k : ℕ)
    (hboundary : ∀ m ∈ NS q k, C.d q (q + 1) m = 0 →
      ∃ y : C.X (q - 1), y ∈ NS (q - 1) (k - 1) ∧ C.d (q - 1) q y = m)
    (x : P.X q) (hx : x ∈ I ^ k • (⊤ : Submodule R (P.X q)))
    (hdx : P.d q (q + 1) x = 0) :
    ∃ y : P.X (q - 1), y ∈ I ^ (k - 1) • (⊤ : Submodule R (P.X (q - 1))) ∧
      P.d (q - 1) q y = x := by
  obtain ⟨m, hm, hem, hdm⟩ := exists_closed_lift NS E I himage hinj hdegree q k x hx hdx
  obtain ⟨y, hy, hdy⟩ := hboundary m hm hdm
  refine ⟨E.f (q - 1) y, ?_, ?_⟩
  · rw [← himage]
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  · rw [differential_eval E, hdy, hem]

include hinj in
/-- A high enough shifted adic tail is acyclic, by actual lifting of every closed
element to a boundary in the previous tail term. Boundary lifting is needed only
in the finite range of degrees in which the target can be nonzero. -/
theorem tail_acyclic_of_graded_boundary_lifting_on_interval
    (b h : ℕ)
    (hbounded : ∀ q : ℤ, q < -(h : ℤ) ∨ 0 < q → IsZero (P.X q))
    (hboundary : ∀ q ∈ Finset.Icc (-(h : ℤ)) 0, ∀ k, b ≤ k → 1 ≤ k → ∀ m ∈ NS q k,
      C.d q (q + 1) m = 0 →
      ∃ y : C.X (q - 1), y ∈ NS (q - 1) (k - 1) ∧ C.d (q - 1) q y = m)
    (n : ℕ) (hn : b + h + 1 ≤ n) :
    ∀ q : ℤ, IsZero ((AdicFilteredComplex.tail P I
      (differential_range_le NS E I himage hdegree) (n : ℤ)).homology q) := by
  let T := AdicFilteredComplex.tail P I (differential_range_le NS E I himage hdegree) (n : ℤ)
  intro q
  by_cases hq : q < -(h : ℤ) ∨ 0 < q
  · apply isZero_homology_of_isZero_X T q
    let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp (hbounded q hq)
    change IsZero (ModuleCat.of R (AdicFilteredComplex.term P I (n : ℤ) q))
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  · apply (HomologicalComplex.exactAt_iff_isZero_homology T q).mp
    rw [HomologicalComplex.exactAt_iff' T (q - 1) q (q + 1)
      (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    change ∀ x : AdicFilteredComplex.term P I (n : ℤ) q,
      T.d q (q + 1) x = 0 → ∃ y : AdicFilteredComplex.term P I (n : ℤ) (q - 1),
        T.d (q - 1) q y = x
    intro x hx
    change T.d q (q + 1) x = 0 at hx
    have hdx : P.d q (q + 1) (x : P.X q) = 0 := congrArg Subtype.val hx
    let k := ((n : ℤ) + q).toNat
    have hk : b ≤ k := by dsimp [k]; omega
    have hkpos : 1 ≤ k := by dsimp [k]; omega
    have hqmem : q ∈ Finset.Icc (-(h : ℤ)) 0 := by
      rw [Finset.mem_Icc]
      omega
    obtain ⟨y, hy, hdy⟩ := exists_adic_boundary NS E I himage hinj hdegree q k
      (hboundary q hqmem k hk hkpos) (x : P.X q) x.2 hdx
    have hprev : ((n : ℤ) + (q - 1)).toNat = k - 1 := by dsimp [k]; omega
    have hyT : y ∈ AdicFilteredComplex.term P I (n : ℤ) (q - 1) := by
      change y ∈ I ^ ((n : ℤ) + (q - 1)).toNat • (⊤ : Submodule R (P.X (q - 1)))
      rwa [hprev]
    refine ⟨⟨y, hyT⟩, ?_⟩
    apply Subtype.ext
    exact hdy

include hinj in
/-- The unrestricted boundary-lifting hypothesis implies the interval version. -/
theorem tail_acyclic_of_graded_boundary_lifting
    (b h : ℕ)
    (hbounded : ∀ q : ℤ, q < -(h : ℤ) ∨ 0 < q → IsZero (P.X q))
    (hboundary : ∀ q k, b ≤ k → 1 ≤ k → ∀ m ∈ NS q k,
      C.d q (q + 1) m = 0 →
      ∃ y : C.X (q - 1), y ∈ NS (q - 1) (k - 1) ∧ C.d (q - 1) q y = m)
    (n : ℕ) (hn : b + h + 1 ≤ n) :
    ∀ q : ℤ, IsZero ((AdicFilteredComplex.tail P I
      (differential_range_le NS E I himage hdegree) (n : ℤ)).homology q) :=
  tail_acyclic_of_graded_boundary_lifting_on_interval NS E I himage hinj hdegree b h hbounded
    (fun q _ => hboundary q) n hn

end SerrePositivity.KoszulMultiplicity

end AdicExactness

section Acyclic

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory CategoryTheory.Limits Filter KoszulMultiplicity

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)

include hz

/-- The actual Koszul differential has coefficients in the parameter ideal. -/
theorem koszulComplex_differential_range_le :
    ∀ q, ((koszulComplex z).d q (q + 1)).hom.range ≤ I • ⊤ :=
  differential_range_le (sourceTermGrade R I z hz)
    (evaluationChainMapR R I z hz) I (map_sourceTermGrade R I z hz)
    (sourceTermGrade_differential R I z hz)

/-- The actual shifted adic Koszul tail is acyclic for all sufficiently large indices. -/
theorem eventually_adicTail_acyclic [IsNoetherianRing R] :
    ∀ᶠ n : ℕ in atTop, ∀ q,
      IsZero ((AdicFilteredComplex.tail (koszulComplex z) I
        (koszulComplex_differential_range_le R I z hz) (n : ℤ)).homology q) := by
  obtain ⟨b, _, hbound⟩ := exists_uniform_bound_source_boundary R I z hz
  apply eventually_atTop.mpr
  refine ⟨b + h + 1, fun n hn => ?_⟩
  exact KoszulMultiplicity.tail_acyclic_of_graded_boundary_lifting
    (sourceTermGrade R I z hz) (evaluationChainMapR R I z hz) I
    (map_sourceTermGrade R I z hz) (injOn_sourceTermGrade R I z hz)
    (sourceTermGrade_differential R I z hz) b h
    (fun q hq => hq.elim (koszulComplex_isZero_X_of_lt z q) (koszulComplex_isZero_X_of_pos z q))
    (fun q k hk _ => hbound q k hk) n hn

end SerrePositivity.KoszulMultiplicity

end Acyclic
