module

public import SerrePositivity.AlgebraicGeometry.CechSingleAugmentationQuasiIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：定数余単体の同じ交代余面複体と、元の零次 single を比較する。
方針：元の微分の0/恒等の公式と、既存のsingle増大の判定を使う。
規約：係数環と加群の宇宙を分け、各成分の全射性は仮定しない。
使われ方：平坦な二重 Čech の全縦次数の増大列を元の増大項へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u v
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)

/-- 定数余単体図式を、同じ既存の交代余面複体関手で写した列。 -/
def cechConstantComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} R)).obj
    ((Functor.const SimplexCategory).obj A)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ定数列の微分は、元の交代和により0と恒等を交互に取る。 -/
theorem cechConstantComplex_d (n : ℕ) :
    (cechConstantComplex A).d n (n + 1) = if Even (n + 2) then 0 else 𝟙 A := by
  dsimp only [cechConstantComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (𝟙 A)) = _
  rw [← Finset.sum_smul, Fin.sum_neg_one_pow]
  split_ifs <;> simp only [zero_smul, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ定数列は、元の0/恒等の微分により正次数で完全。 -/
theorem cechConstantComplex_exact (n : ℕ) : (cechConstantComplex A).ExactAt (n + 1) := by
  let C := cechConstantComplex A
  rw [C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) ((n + 1) + 1)).hom
  change Function.Exact ((cechConstantComplex A).d n (n + 1)).hom
    ((cechConstantComplex A).d (n + 1) ((n + 1) + 1)).hom
  by_cases h : Even (n + 2)
  · have h' : ¬ Even ((n + 1) + 2) := by
      simp only [Nat.even_iff] at h ⊢
      omega
    rw [cechConstantComplex_d, cechConstantComplex_d, ite_eq_left h, ite_eq_right h']
    change Function.Exact (0 : A →ₗ[R] A) (LinearMap.id : A →ₗ[R] A)
    exact (LinearMap.exact_zero_iff_injective A LinearMap.id).mpr Function.injective_id
  · have h' : Even ((n + 1) + 2) := by
      simp only [Nat.even_iff] at h ⊢
      omega
    rw [cechConstantComplex_d, cechConstantComplex_d, ite_eq_right h, ite_eq_left h']
    change Function.Exact (LinearMap.id : A →ₗ[R] A) (0 : A →ₗ[R] A)
    exact (LinearMap.exact_zero_iff_surjective A LinearMap.id).mpr Function.surjective_id

set_option backward.isDefEq.respectTransparency false in
/-- 同じ零次 single から、元の定数列への標準的な包含。 -/
def cechConstantSingleAugmentation :
    (HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) 0).obj A ⟶ cechConstantComplex A :=
  HomologicalComplex.mkHomFromSingle (𝟙 A) (by
    intro k hk
    have he : k = 1 := Eq.symm hk
    subst k
    rw [cechConstantComplex_d, ite_eq_left (show Even 2 by decide), comp_zero])

set_option backward.isDefEq.respectTransparency false in
/-- 同じ包含の零次成分は、元の single の標準同型。 -/
theorem cechConstantSingleAugmentation_f_zero :
    (cechConstantSingleAugmentation A).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom := by
  rw [cechConstantSingleAugmentation, HomologicalComplex.mkHomFromSingle_f, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ零次 single から定数列への包含は、元の増大を保つ準同型。 -/
theorem cechConstantSingleAugmentation_quasiIso : QuasiIso (cechConstantSingleAugmentation A) := by
  constructor
  intro q
  apply cechSingleAugmentation_quasiIsoAt A (cechConstantComplex A)
    (cechConstantSingleAugmentation A) ?_ ?_ (cechConstantComplex_exact A) q
  · rw [cechConstantSingleAugmentation_f_zero]
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · rw [cechConstantSingleAugmentation_f_zero, cechConstantComplex_d,
      ite_eq_left (show Even 2 by decide)]
    change Function.Exact (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom.hom
      (0 : A →ₗ[R] A)
    apply (LinearMap.exact_zero_iff_surjective A _).mpr
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance

end SerrePositivity.AlgebraicGeometry
