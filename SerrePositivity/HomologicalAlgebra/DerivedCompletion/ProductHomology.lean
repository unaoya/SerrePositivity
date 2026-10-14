module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplex
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import SerrePositivity.HomologicalAlgebra.ConeLES
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # 加群複体の直積とホモロジー

直積のホモロジーを各成分のホモロジーの直積へ同定する。
サイクルと境界の代表元を成分ごとに選ぶため、遷移の全射性は不要である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 複体の直積の各次数を、成分の項の直積へ同定する。 -/
def complexProductDegreeEquiv (i : ℤ) :
    (piObj K).X i ≃ₗ[R] ∀ n, (K n).X i :=
  ((PreservesProduct.iso (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) K)
    ≪≫ ModuleCat.piIsoPi (fun n ↦ (K n).X i)).toLinearEquiv

@[simp] theorem complexProductDegreeEquiv_apply (i : ℤ) (x : (piObj K).X i) (n : ℕ) :
    complexProductDegreeEquiv R K i x n = (Pi.π K n).f i x := by
  have h := ModuleCat.piIsoPi_hom_ker_subtype (fun n ↦ (K n).X i) n
  have h' := piComparison_comp_π
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) K n
  exact congrArg (fun f ↦ f.hom x) ((congrArg
    (fun f ↦ (PreservesProduct.iso
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) K).hom ≫ f) h).trans h')

/-- 直積のホモロジーから各成分のホモロジーへの標準比較写像。 -/
def complexProductHomologyMap (i : ℤ) :
    (piObj K).homology i →ₗ[R] ∀ n, (K n).homology i :=
  LinearMap.pi (fun n ↦ (HomologicalComplex.homologyMap (Pi.π K n) i).hom)

/-- 各成分のホモロジー類は、直積の一つのサイクルで表せる。 -/
theorem complexProductHomologyMap_surjective (i : ℤ) :
    Function.Surjective (complexProductHomologyMap R K i) := by
  intro x
  have hrep : ∀ n, ∃ z : (K n).cycles i, (K n).homologyπ i z = x n :=
    fun n ↦ (ModuleCat.epi_iff_surjective ((K n).homologyπ i)).mp inferInstance (x n)
  choose z hz using hrep
  let y := (complexProductDegreeEquiv R K i).symm (fun n ↦ (K n).iCycles i (z n))
  have hy : ∀ n, (Pi.π K n).f i y = (K n).iCycles i (z n) := by
    intro n
    rw [← complexProductDegreeEquiv_apply]
    exact congrFun ((complexProductDegreeEquiv R K i).apply_symm_apply _) n
  let j := (ComplexShape.up ℤ).next i
  have hdy : (piObj K).d i j y = 0 := by
    apply (complexProductDegreeEquiv R K j).injective
    ext n
    simp only [complexProductDegreeEquiv_apply, map_zero]
    have hcomm := congrArg (fun f ↦ f.hom y) ((Pi.π K n).comm i j)
    change (K n).d i j ((Pi.π K n).f i y) =
      (Pi.π K n).f j ((piObj K).d i j y) at hcomm
    rw [← hcomm, hy]
    exact congrArg (fun f ↦ f.hom (z n)) ((K n).iCycles_d i j)
  let y' : (piObj K).cycles i := ((piObj K).sc i).cyclesMk y hdy
  have hy' : ∀ n, HomologicalComplex.cyclesMap (Pi.π K n) i y' = z n := by
    intro n
    apply (ModuleCat.mono_iff_injective ((K n).iCycles i)).mp inferInstance
    have h := congrArg (fun f ↦ f.hom y') (HomologicalComplex.cyclesMap_i (Pi.π K n) i)
    change (K n).iCycles i (HomologicalComplex.cyclesMap (Pi.π K n) i y') =
      (Pi.π K n).f i ((piObj K).iCycles i y') at h
    have hyy : (piObj K).iCycles i y' = y := ((piObj K).sc i).i_cyclesMk y hdy
    rw [h, hyy, hy]
  refine ⟨(piObj K).homologyπ i y', ?_⟩
  ext n
  change HomologicalComplex.homologyMap (Pi.π K n) i ((piObj K).homologyπ i y') = x n
  have h := congrArg (fun f ↦ f.hom y')
    (HomologicalComplex.homologyπ_naturality (Pi.π K n) i)
  change HomologicalComplex.homologyMap (Pi.π K n) i ((piObj K).homologyπ i y') =
    (K n).homologyπ i (HomologicalComplex.cyclesMap (Pi.π K n) i y') at h
  rw [h, hy', hz]

/-- 各成分で境界になる直積のサイクルは、直積でも境界になる。 -/
theorem complexProductHomologyMap_injective (i : ℤ) :
    Function.Injective (complexProductHomologyMap R K i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((piObj K).homologyπ i)).mp inferInstance x
  let j := (ComplexShape.up ℤ).prev i
  have hb : ∀ n, ∃ b : (K n).X j,
      (K n).toCycles j i b = HomologicalComplex.cyclesMap (Pi.π K n) i z := by
    intro n
    let S := (K n).sc i
    let E := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
    have hE : E.Exact := E.exact_of_g_is_cokernel S.homologyIsCokernel
    have hz : (K n).homologyπ i (HomologicalComplex.cyclesMap (Pi.π K n) i z) = 0 := by
      have h := congrArg (fun f ↦ f.hom z)
        (HomologicalComplex.homologyπ_naturality (Pi.π K n) i)
      exact h.symm.trans (congrFun hx n)
    exact E.moduleCat_exact_iff.mp hE _ hz
  choose b hb using hb
  let y := (complexProductDegreeEquiv R K j).symm b
  have hy : ∀ n, (Pi.π K n).f j y = b n := by
    intro n
    rw [← complexProductDegreeEquiv_apply]
    exact congrFun ((complexProductDegreeEquiv R K j).apply_symm_apply _) n
  have hboundary : (piObj K).toCycles j i y = z := by
    apply (ModuleCat.mono_iff_injective ((piObj K).iCycles i)).mp inferInstance
    apply (complexProductDegreeEquiv R K i).injective
    ext n
    simp only [complexProductDegreeEquiv_apply]
    have h₁ := congrArg (fun f ↦ f.hom y) ((piObj K).toCycles_i j i)
    have h₂ := congrArg (fun f ↦ f.hom y) ((Pi.π K n).comm j i)
    have h₃ := congrArg (fun f ↦ f.hom z) (HomologicalComplex.cyclesMap_i (Pi.π K n) i)
    have h₄ := congrArg (fun f ↦ f.hom (b n)) ((K n).toCycles_i j i)
    have h₅ := congrArg (fun w ↦ (K n).iCycles i w) (hb n)
    change (K n).d j i ((Pi.π K n).f j y) =
      (Pi.π K n).f i ((piObj K).d j i y) at h₂
    change (piObj K).iCycles i ((piObj K).toCycles j i y) = (piObj K).d j i y at h₁
    change (K n).iCycles i (HomologicalComplex.cyclesMap (Pi.π K n) i z) =
      (Pi.π K n).f i ((piObj K).iCycles i z) at h₃
    change (K n).iCycles i ((K n).toCycles j i (b n)) = (K n).d j i (b n) at h₄
    rw [h₁, ← h₂, hy]
    exact h₄.symm.trans (h₅.trans h₃)
  rw [← hboundary]
  exact congrArg (fun f ↦ f.hom y) ((piObj K).toCycles_comp_homologyπ j i)

/-- 任意の次数で、加群複体の直積とホモロジーは可換。 -/
def complexProductHomologyEquiv (i : ℤ) :
    (piObj K).homology i ≃ₗ[R] ∀ n, (K n).homology i :=
  LinearEquiv.ofBijective (complexProductHomologyMap R K i)
    ⟨complexProductHomologyMap_injective R K i, complexProductHomologyMap_surjective R K i⟩

@[simp] theorem complexProductHomologyEquiv_apply (i : ℤ)
    (x : (piObj K).homology i) (n : ℕ) :
    complexProductHomologyEquiv R K i x n = HomologicalComplex.homologyMap (Pi.π K n) i x := rfl

/-- 直積の同定の下で、ホモロジー上の差分も成分の差分になる。 -/
theorem complexProductHomologyEquiv_difference (t : ∀ n, K (n + 1) ⟶ K n)
    (i : ℤ) (x : (piObj K).homology i) :
    complexProductHomologyEquiv R K i
      (HomologicalComplex.homologyMap (complexTowerDifference R K t) i x) =
    moduleTowerDifference R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom)
        (complexProductHomologyEquiv R K i x) := by
  ext n
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f i)
    (complexTowerDifference_projection R K t n)
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_sub] at h
  exact congrArg (fun f ↦ f.hom x) h

end SerrePositivity.DerivedCompletion
