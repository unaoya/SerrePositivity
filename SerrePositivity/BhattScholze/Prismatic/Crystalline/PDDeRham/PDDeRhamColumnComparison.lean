module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnPoincare
public import Mathlib.Algebra.Homology.SingleHomology
public import SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCollapse
import all SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
# pd de Rham 総複体から第 0 列への擬同型

## 概要
標数 p の列を差座標のない定数列に比較し、第 0 列への射影の擬同型を得る。

## 方針
定数余単体の行は正次数で完全。定数列双複体を第 0 列だけの双複体に比較する。

## 規約
総複体の符号は横次数で付ける。

## 使われ方
pd Čech コホモロジーと多項式 de Rham コホモロジーの比較。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "up" => ComplexShape.up ℕ
local notation "C" => pdDeRhamColumn p k r ⦋0⦌
local notation "K" => pdDeRhamConstantColumn p k r
private abbrev singleColumn := (CochainComplex.single₀ (CochainComplex (ModuleCat.{u} k) ℕ)).obj C
local notation "L" => singleColumn p k r

private theorem constRow_d (i j : ℕ) :
    (constRowComplex p k r j).d i (i + 1) = if Even i then 0 else 𝟙 ((C).X j) := by
  change (AlternatingCofaceMapComplex.obj (constColumnRow p k r j)).d i (i + 1) = _
  dsimp only [AlternatingCofaceMapComplex.obj, CochainComplex.of]
  rw [CochainComplex.of_d]
  simp [AlternatingCofaceMapComplex.objD, constColumnRow, CosimplicialObject.δ,
    ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add]

private theorem constRow_exact (a b : ℕ) (ha : a ≠ 0) :
    (constRowComplex p k r b).ExactAt a := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  apply ((constRowComplex p k r b).exactAt_iff' a (a + 1) (a + 2) (CochainComplex.prev_nat_succ a) (CochainComplex.next ℕ (a + 1))).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change (constRowComplex p k r b).d (a + 1) (a + 2) x = 0 at hx
  change ∃ y, (constRowComplex p k r b).d a (a + 1) y = x
  by_cases ha : Even a
  · have hb : ¬ Even (a + 1) := by simpa [Nat.even_add_one]
    rw [constRow_d, ite_eq_right hb] at hx
    exact ⟨0, (map_zero _).trans hx.symm⟩
  · rw [constRow_d, ite_eq_right ha]
    exact ⟨x, rfl⟩

private def constantColumnTruncate : K ⟶ L :=
  (CochainComplex.toSingle₀Equiv K C).symm (𝟙 C)

private theorem constantColumnTruncate_zero :
    (constantColumnTruncate p k r).f 0 = 𝟙 C := by
  exact (CochainComplex.toSingle₀Equiv K C).apply_symm_apply (𝟙 C)

private theorem truncation_row_quasiIso (b : ℕ) :
    QuasiIso ((bicomplexRowFunctor (R := k) b).map (constantColumnTruncate p k r)) := by
  let f := (bicomplexRowFunctor (R := k) b).map (constantColumnTruncate p k r)
  constructor
  intro a
  rw [quasiIsoAt_iff_isIso_homologyMap]
  cases a with
  | zero =>
    let F := (shortComplexFunctor (ModuleCat.{u} k) up 0).map f
    have h₁ : Epi F.τ₁ := by
      change Epi (((constantColumnTruncate p k r).f ((ComplexShape.up ℕ).prev 0)).f b)
      rw [CochainComplex.prev_nat_zero, constantColumnTruncate_zero]
      change Epi (𝟙 ((C).X b))
      infer_instance
    have h₂ : IsIso F.τ₂ := by
      change IsIso (((constantColumnTruncate p k r).f 0).f b)
      rw [constantColumnTruncate_zero]
      change IsIso (𝟙 ((C).X b))
      infer_instance
    have hS : (((bicomplexRowFunctor (R := k) b).obj K).sc 0).g = 0 := by
      change (constRowComplex p k r b).d 0 ((ComplexShape.up ℕ).next 0) = 0
      rw [CochainComplex.next ℕ 0]
      simp [constRow_d]
    have hT : (((bicomplexRowFunctor (R := k) b).obj L).sc 0).g = 0 := by
      change ((L).d 0 ((ComplexShape.up ℕ).next 0)).f b = 0
      rw [single_obj_d]
      rfl
    have : IsIso (((bicomplexRowFunctor (R := k) b).obj K).sc 0).iCycles := (((bicomplexRowFunctor (R := k) b).obj K).sc 0).cyclesIsoX₂ hS |>.isIso_hom
    have : IsIso (((bicomplexRowFunctor (R := k) b).obj L).sc 0).iCycles := (((bicomplexRowFunctor (R := k) b).obj L).sc 0).cyclesIsoX₂ hT |>.isIso_hom
    have hI : IsIso (ShortComplex.cyclesMap F ≫ (((bicomplexRowFunctor (R := k) b).obj L).sc 0).iCycles) := by
      rw [ShortComplex.cyclesMap_i]
      infer_instance
    exact ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi
      (IsIso.of_isIso_comp_right _ ((((bicomplexRowFunctor (R := k) b).obj L).sc 0).iCycles)) h₁
  | succ a =>
    have hx := (constRow_exact p k r (a + 1) b (Nat.succ_ne_zero _)).isZero_homology
    have hy : IsZero (((bicomplexRowFunctor (R := k) b).obj L).homology (a + 1)) := by
      apply ShortComplex.isZero_homology_of_isZero_X₂
      change IsZero (((L).X (a + 1)).X b)
      exact (HomologicalComplex.eval _ _ b).map_isZero
        (isZero_single_obj_X up 0 C (a + 1) (Nat.succ_ne_zero _))
    have h : homologyMap f (a + 1) = (hx.iso hy).hom := hx.eq_of_src _ _
    rw [h]
    exact (hx.iso hy).isIso_hom

private theorem constantColumnTruncate_total_quasiIso :
    QuasiIso (HomologicalComplex₂.total.map (constantColumnTruncate p k r) up) := by
  apply bicomplexTotal_quasiIso_of_rows
  · exact truncation_row_quasiIso p k r
  · intro a b
    cases a with
    | zero =>
      rw [constantColumnTruncate_zero]
      exact Function.surjective_id
    | succ a =>
      intro x
      refine ⟨0, ?_⟩
      have h : IsZero (((L).X (a + 1)).X b) :=
        (HomologicalComplex.eval _ _ b).map_isZero
          (isZero_single_obj_X up 0 C (a + 1) (Nat.succ_ne_zero _))
      exact (ModuleCat.isZero_iff_subsingleton.mp h).elim _ _

private theorem singleColumnProjection_isIso :
    IsIso (totalToColumnZero (L)) := by
  let M := (L)
  let f := totalToColumnZero M
  have (n : ℕ) : IsIso (f.f n) := by
    let i := HomologicalComplex₂.ιTotal M up 0 n n (Nat.zero_add _)
    have h₁ : i ≫ f.f n = 𝟙 _ := by
      simp [i, f, totalToColumnZero, columnZeroApp]
    have h₂ : f.f n ≫ i = 𝟙 _ := by
      apply HomologicalComplex₂.total.hom_ext
      intro a b h
      by_cases ha : a = 0
      · subst a
        have hb : b = n := by simpa using h
        subst b
        change i ≫ f.f n ≫ i = i ≫ 𝟙 _
        rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]
      · have hz : IsZero ((M.X a).X b) :=
          (HomologicalComplex.eval _ _ b).map_isZero (isZero_single_obj_X up 0 C a ha)
        exact hz.eq_of_src _ _
    exact ⟨⟨i, h₂, h₁⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components f

private theorem constantColumnTruncate_projection :
    HomologicalComplex₂.total.map (constantColumnTruncate p k r) up ≫ totalToColumnZero (L) =
      totalToColumnZero (K) := by
  ext n : 1
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc]
  by_cases ha : a = 0
  · subst a
    have hb : b = n := by simpa using h
    subst b
    simp [constantColumnTruncate_zero, totalToColumnZero, columnZeroApp]
    rfl
  · simp [ha, totalToColumnZero, columnZeroApp]

private theorem constantColumnProjection_quasiIso : QuasiIso (totalToColumnZero (K)) := by
  rw [← constantColumnTruncate_projection p k r]
  let := constantColumnTruncate_total_quasiIso p k r
  let := singleColumnProjection_isIso p k r
  infer_instance

private theorem pdDeRhamCollapse_projection :
    HomologicalComplex₂.total.map (pdDeRhamCollapse p k r) up ≫ totalToColumnZero (K) =
      pdDeRhamColumnZeroProjection p k r := by
  ext n : 1
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc]
  by_cases ha : a = 0
  · subst a
    have hb : b = n := by simpa using h
    subst b
    have hc : (pdRow p k r n).map (collapseSimplex ⦋0⦌) = 𝟙 _ := by
      rw [collapseSimplex, SimplexCategory.const_eq_id]
      exact (pdRow p k r n).map_id _
    simp [pdDeRhamCollapse, pdDeRhamColumnCollapse, pdDeRhamColumnMap, hc,
      pdDeRhamColumnZeroProjection, totalToColumnZero, columnZeroApp]
    rfl
  · simp [ha, pdDeRhamColumnZeroProjection, totalToColumnZero, columnZeroApp]

/-- 標数 p では、pd de Rham 総複体から第 0 列への射影は擬同型。 -/
theorem pdDeRhamColumnZeroProjection_quasiIso (hp : (p : k) = 0) :
    QuasiIso (pdDeRhamColumnZeroProjection p k r) := by
  rw [← pdDeRhamCollapse_projection p k r]
  let := pdDeRhamCollapse_total_quasiIso k r p hp
  let := constantColumnProjection_quasiIso p k r
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
