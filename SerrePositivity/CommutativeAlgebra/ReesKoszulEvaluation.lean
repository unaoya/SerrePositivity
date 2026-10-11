module

public import SerrePositivity.CommutativeAlgebra.KoszulReesFinite
public import SerrePositivity.CommutativeAlgebra.GradedReesSelf
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.CommutativeAlgebra.GradedKoszulEvaluation

/-! # Rees 加群の t = 1 評価と Koszul 複体

Rees 代数を t = 1 で評価すると、次数一の生成元 z_i t が z_i に送られる。
多項式環の変数 X_i による Koszul 構成から、元の列 z_i の Koszul 複体への射を作る。
係数次数 n の評価は I^n に値をもち、その次数成分では線形同型である。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.ReesKoszulEvaluation

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

/-- 評価による多項式作用と、係数環自身の作用は両立する。 -/
theorem evaluatedModule_scalarTower {h : ℕ} (z : Fin h → R) :
    let _ := evaluatedModule R z
    IsScalarTower R (MvPolynomial (Fin h) R) R := by
  let := evaluatedModule R z
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change MvPolynomial.aeval z (algebraMap R (MvPolynomial (Fin h) R) r) * m = r * m
  rw [(MvPolynomial.aeval z).commutes]
  rfl

/-- Rees 加群の評価は、両側を対応する評価による多項式加群として見ると線形である。 -/
def evaluation {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    let _ := KoszulReesFinite.reesPolynomialModule R I R z hz
    let _ := evaluatedModule R z
    ReesModule R I R →ₗ[MvPolynomial (Fin h) R] R := by
  let := KoszulReesFinite.reesPolynomialModule R I R z hz
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
  let _ := KoszulReesFinite.reesPolynomialModule R I R z hz
  ModuleCat.of _ (ReesModule R I R)

/-- 係数環を X_i ↦ z_i に沿って係数制限した、多項式環上の対象。 -/
def targetModule {h : ℕ} (z : Fin h → R) : ModuleCat.{u} (MvPolynomial (Fin h) R) :=
  (ModuleCat.restrictScalars (MvPolynomial.aeval z).toRingHom).obj (ModuleCat.of R R)

/-- 多項式加群としての t = 1 評価射。 -/
def evaluationHom {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I) :
    sourceModule R I z hz ⟶ targetModule R z := by
  let := KoszulReesFinite.reesPolynomialModule R I R z hz
  let := evaluatedModule R z
  exact ModuleCat.ofHom (evaluation R I z hz)

/-- 多項式作用を係数環へ制限しても、元の Rees 加群の係数作用に戻る。 -/
def sourceCoefficientEquiv {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) :
    (ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj
      (sourceModule R I z hz) ≃ₗ[R] ReesModule R I R := by
  let := KoszulReesFinite.reesPolynomialModule R I R z hz
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
        (GradedKoszulEvaluation.termMap MvPolynomial.X (evaluationHom R I z hz) q) := by
  ext m
  rfl

/-- 各 Koszul 項の係数次数 n の評価像は、その項の I^n 倍に一致する。 -/
theorem map_sourceTermGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (q : ℤ) (n : ℕ) :
    (sourceTermGrade R I z hz q n).map ((evaluationChainMapR R I z hz).f q).hom =
      (I ^ n • ⊤ : Submodule R ((koszulComplex z).X q)) := by
  rw [evaluationChainMapR_term, Submodule.map_comp]
  have hm := GradedKoszulEvaluation.map_termGrade MvPolynomial.X (evaluationHom R I z hz)
    (sourceCoefficientGrade R I z hz) (fun n ↦ I ^ n • ⊤)
    (map_sourceCoefficientGrade R I z hz) q n
  rw [sourceTermGrade, hm, GradedKoszulEvaluation.termGrade_ideal_smul_top,
    Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (targetTermEquiv R z q).surjective]

/-- 各 Koszul 項の係数次数成分に制限した評価は単射である。 -/
theorem injOn_sourceTermGrade {h : ℕ} (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = I) (q : ℤ) (n : ℕ) :
    Set.InjOn ((evaluationChainMapR R I z hz).f q).hom
      {a | a ∈ sourceTermGrade R I z hz q n} := by
  intro a ha b hb hab
  rw [evaluationChainMapR_term] at hab
  exact GradedKoszulEvaluation.injOn_termGrade MvPolynomial.X (evaluationHom R I z hz)
    (sourceCoefficientGrade R I z hz) (injOn_sourceCoefficientGrade R I z hz) q n
    ha hb ((targetTermEquiv R z q).injective hab)

end SerrePositivity.ReesKoszulEvaluation
