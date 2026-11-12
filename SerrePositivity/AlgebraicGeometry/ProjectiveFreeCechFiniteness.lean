module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartAdditive
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartShift
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedFree
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteRetracts

/-!
概要：有限個の多項式環の捻りの自由加群の Čech コホモロジーは有限生成。
方針：各成分の射影と包含の分裂を、標準開の図式と Čech コホモロジーへ送る。
規約：有限個の生成元の次数を整数で指定する。
使われ方：有限斉次自由表示から一般の有限生成加群へ降下帰納する際の入力。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped BigOperators

/-- 有限自由加群の各生成元に次数を指定すると、係数環の作用は次数を保つ。 -/
instance projectiveGradedFreePieceSMul
    {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype κ]
    (A : ℤ → Submodule R S) [SetLike.GradedMonoid A] (degree : κ → ℤ) :
    SetLike.GradedSMul A (projectiveGradedFreePiece A degree) where
  smul_mem {i j} {a m} ha hm := by
    change ∀ k ∈ Set.univ, a * m k ∈ A (i + j - degree k)
    intro k hk
    have h := SetLike.mul_mem_graded ha (hm k hk)
    simpa only [add_sub_assoc] using h

private theorem projectiveGradedFreeSingle_mem
    {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype κ] [DecidableEq κ]
    (A : ℤ → Submodule R S) (degree : κ → ℤ) (k : κ) (d : ℤ) (m : S)
    (hm : m ∈ A (d - degree k)) :
    LinearMap.single S (fun _ : κ ↦ S) k m ∈ projectiveGradedFreePiece A degree d := by
  change ∀ j ∈ Set.univ, (Pi.single k m : κ → S) j ∈ A (d - degree j)
  intro j _
  by_cases h : j = k
  · subst j
    simpa using hm
  · simp [h]

universe u v

variable {R : Type u} {ι : Type v} [CommRing R] [IsNoetherianRing R]
variable [LinearOrder ι] [Fintype ι]
variable {κ : Type (max u v)} [Fintype κ] [DecidableEq κ]

/-- 有限個の多項式環の捻りからなる自由加群の狭義増加 Čech コホモロジーは有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveFreeOrderedCechHomology_finite (degree : κ → ℤ) (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((orderedCechComplex (projectiveGradedModuleChartDiagram (ι := ι)
        (projectiveGradedFreePiece
          (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) degree) d)).homology q) := by
  classical
  let S := MvPolynomial ι R
  let A := AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
  let G := projectiveGradedFreePiece A degree
  let D := projectiveGradedModuleChartDiagram (ι := ι) G d
  letI (k : κ) : SetLike.GradedSMul A (fun n ↦ A (n - degree k)) :=
    projectivePolynomialShiftSMul (R := R) (ι := ι) (degree k)
  let E (k : κ) := projectiveGradedModuleChartDiagram (ι := ι) (fun n ↦ A (n - degree k)) d
  let proj (k : κ) : (κ → S) →ₗ[S] S := LinearMap.proj k
  let incl (k : κ) : S →ₗ[S] κ → S := LinearMap.single S (fun _ : κ ↦ S) k
  have hp (k : κ) : ∀ n, ∀ m ∈ G n, proj k m ∈ A (n - degree k) :=
    fun n m hm ↦ hm k (Set.mem_univ k)
  have hi (k : κ) : ∀ n, ∀ m ∈ A (n - degree k), incl k m ∈ G n :=
    fun n m hm ↦ projectiveGradedFreeSingle_mem A degree k n m hm
  let p (k : κ) : D ⟶ E k := projectiveGradedModuleChartMap (ι := ι)
    G (fun n ↦ A (n - degree k)) d (proj k) (hp k)
  let i (k : κ) : E k ⟶ D := projectiveGradedModuleChartMap (ι := ι)
    (fun n ↦ A (n - degree k)) G d (incl k) (hi k)
  let f (k : κ) := (incl k).comp (proj k)
  have hf (k : κ) : ∀ n, ∀ m ∈ G n, f k m ∈ G n :=
    fun n m hm ↦ hi k n _ (hp k n m hm)
  have hsum : ∑ k, f k = LinearMap.id := by
    apply LinearMap.ext
    intro m
    simp only [LinearMap.sum_apply, LinearMap.id_apply, f, LinearMap.comp_apply,
      incl, proj, LinearMap.proj_apply]
    exact LinearMap.sum_single_apply (fun _ : κ ↦ S) m
  have hfsum : ∀ n, ∀ m ∈ G n, (∑ k, f k) m ∈ G n := by
    intro n m hm
    simpa only [hsum, LinearMap.id_apply] using hm
  have hD : ∑ k, p k ≫ i k = 𝟙 D := by
    calc
      ∑ k, p k ≫ i k =
          ∑ k, projectiveGradedModuleChartMap (ι := ι) G G d (f k) (hf k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact projectiveGradedModuleChartMap_comp
          G (fun n ↦ A (n - degree k)) G d (proj k) (incl k) (hp k) (hi k)
      _ = projectiveGradedModuleChartMap (ι := ι) G G d (∑ k, f k) hfsum :=
        (projectiveGradedModuleChartMap_sum G G d Finset.univ f hf hfsum).symm
      _ = 𝟙 D := by
        simpa only [hsum] using projectiveGradedModuleChartMap_id G d
  let C := orderedCechComplexFunctor (R := R) (ι := ι)
  have hK : ∑ k, C.map (p k) ≫ C.map (i k) = 𝟙 (orderedCechComplex D) := by
    simp_rw [← C.map_comp]
    rw [← Functor.map_sum, hD, C.map_id]
    rfl
  exact projectiveCechHomology_finite_of_finite_splitting
    (orderedCechComplex D) (fun k ↦ orderedCechComplex (E k))
    (fun k ↦ C.map (p k)) (fun k ↦ C.map (i k)) hK q
    (fun k ↦ projectiveShiftedPolynomialOrderedCechHomology_finite (ι := ι) (degree k) d q)

end SerrePositivity.AlgebraicGeometry
