module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFreeCechFiniteness
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedCechExact
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechDevissage
public import Mathlib.RingTheory.Polynomial.Basic

/-!
概要：有限生成次数付き多項式加群の標準開 Čech コホモロジーは有限生成。
方針：有限斉次自由表示とその核を作り、有界な Čech 複体の長完全列で降下帰納する。
規約：Noether な係数環。加群は多項式環と同じ宇宙に置く。
使われ方：射影的なスキームの構造層と Rees 加群の有限性の計算に使う。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

universe u v

variable {R : Type u} {ι : Type v} [CommRing R] [IsNoetherianRing R]
variable [LinearOrder ι] [Fintype ι]

private structure FiniteGradedPolynomialModule where
  carrier : ModuleCat.{max u v} R
  [polynomialModule : Module (MvPolynomial ι R) carrier]
  [tower : IsScalarTower R (MvPolynomial ι R) carrier]
  grading : ℤ → Submodule R carrier
  [decomposition : DirectSum.Decomposition grading]
  [compatible : SetLike.GradedSMul
    (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) grading]
  [finite : Module.Finite (MvPolynomial ι R) carrier]

private def FiniteGradedPolynomialModule.diagram
    (M : FiniteGradedPolynomialModule (R := R) (ι := ι)) (d : ℤ) :
    Finset ι ⥤ ModuleCat R := by
  letI := M.polynomialModule
  letI := M.tower
  letI := M.compatible
  exact projectiveGradedModuleChartDiagram (ι := ι) M.grading d

private theorem FiniteGradedPolynomialModule.cechFinite
    (M : FiniteGradedPolynomialModule (R := R) (ι := ι)) (d : ℤ) (q : ℕ) :
    Module.Finite R ((orderedCechComplex (M.diagram d)).homology q) := by
  classical
  let D (N : FiniteGradedPolynomialModule (R := R) (ι := ι)) := N.diagram d
  apply projectiveCechFinite_of_shortExact_presentations D ?_ M q
  intro N
  letI := N.polynomialModule
  letI := N.tower
  letI := N.decomposition
  letI := N.compatible
  letI := N.finite
  let S := MvPolynomial ι R
  let A := AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
  obtain ⟨t, ht, hspan⟩ := exists_finset_homogeneous_span_top (S := S) N.grading
  let degree (j : t) : ℤ := (ht j.val j.property).choose
  let v (j : t) : N.carrier := j.val
  have hv (j : t) : v j ∈ N.grading (degree j) := (ht j.val j.property).choose_spec
  let GF := projectiveGradedFreePiece A degree
  letI : DirectSum.Decomposition GF := projectiveGradedFreeDecomposition A degree
  let f : (t → S) →ₗ[S] N.carrier := Fintype.linearCombination S v
  have hf : ∀ n, ∀ x ∈ GF n, f x ∈ N.grading n :=
    fun n x hx ↦ projectiveGradedFreeMap_mem A N.grading degree v hv n ⟨x, hx⟩
  have hrange : Set.range v = (t : Set N.carrier) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact j.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsurj : Function.Surjective f := by
    apply projectiveGradedFreeMap_surjective v
    rw [hrange]
    exact hspan
  let F : FiniteGradedPolynomialModule (R := R) (ι := ι) :=
    { carrier := ModuleCat.of R (t → S)
      polynomialModule := inferInstance
      tower := inferInstance
      grading := GF
      decomposition := projectiveGradedFreeDecomposition A degree
      compatible := inferInstance
      finite := inferInstance }
  let GK := projectiveGradedKernelPiece GF f
  letI : DirectSum.Decomposition GK := projectiveGradedKernelDecomposition GF N.grading f hf
  letI : SetLike.GradedSMul A GK :=
    { smul_mem := by
        intro i j a x ha hx
        change a • x.val ∈ GF (i + j)
        have hx' : x.val ∈ GF j := hx
        exact SetLike.GradedSMul.smul_mem ha hx' }
  let K : FiniteGradedPolynomialModule (R := R) (ι := ι) :=
    { carrier := ModuleCat.of R (LinearMap.ker f)
      polynomialModule := inferInstance
      tower := inferInstance
      grading := GK
      decomposition := projectiveGradedKernelDecomposition GF N.grading f hf
      compatible := inferInstance
      finite := inferInstance }
  let k : (LinearMap.ker f) →ₗ[S] (t → S) := (LinearMap.ker f).subtype
  have hk : ∀ n, ∀ x ∈ GK n, k x ∈ GF n := fun _ _ h ↦ h
  have hex : Function.Exact k f := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.property
  obtain ⟨hzero, hshort⟩ := projectiveOrderedCech_shortExact
    GK GF N.grading d k f hk hf (LinearMap.ker f).injective_subtype hex hsurj
  let C := (ShortComplex.mk
    (projectiveGradedModuleChartMap (ι := ι) GK GF d k hk)
    (projectiveGradedModuleChartMap (ι := ι) GF N.grading d f hf) hzero).map
      (orderedCechComplexFunctor (R := R) (ι := ι))
  refine ⟨F, K, C.f, C.g, C.zero, hshort, ?_⟩
  intro j
  exact projectiveFreeOrderedCechHomology_finite (R := R) (ι := ι) degree d j

/-- 有限生成次数付き多項式加群の各標準開 Čech コホモロジーは係数環上有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveGradedOrderedCechHomology_finite
    {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    (G : ℤ → Submodule R M) [DirectSum.Decomposition G]
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((orderedCechComplex (projectiveGradedModuleChartDiagram (ι := ι) G d)).homology q) := by
  let N : FiniteGradedPolynomialModule (R := R) (ι := ι) :=
    { carrier := ModuleCat.of R M
      polynomialModule := inferInstance
      tower := inferInstance
      grading := G
      decomposition := inferInstance
      compatible := inferInstance
      finite := inferInstance }
  exact N.cechFinite d q

/-- 有限生成次数付き多項式加群の全タプル Čech コホモロジーも係数環上有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveGradedFullCechHomology_finite
    {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    (G : ℤ → Submodule R M) [DirectSum.Decomposition G]
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((fullCechComplex (projectiveGradedModuleChartDiagram (ι := ι) G d)).homology q) := by
  let e := fullCechOrderedHomologyIso (projectiveGradedModuleChartDiagram (ι := ι) G d) q
  letI : Module.Finite R
      ((orderedCechComplex (projectiveGradedModuleChartDiagram (ι := ι) G d)).homology q) :=
    projectiveGradedOrderedCechHomology_finite G d q
  exact Module.Finite.of_surjective e.inv.hom
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

end SerrePositivity.AlgebraicGeometry
