module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
public import SerrePositivity.HomologicalAlgebra.BicomplexComponents
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# pd de Rham 総複体の係数変換

## 概要
双次数の係数変換を総複体にまとめる。

## 方針
有限個の双次数成分へ射影し、還元した成分を挿入し直す。

## 規約
横次数に従う Koszul 符号を保つ。

## 使われ方
整係数で微分を p で割ってから標数 p の余輪体を作る。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)

local notation "KA" => pdDeRhamDoubleComplex p A r
local notation "KB" => pdDeRhamDoubleComplex p B r

set_option backward.isDefEq.respectTransparency false in
/-- 一つの双次数における係数変換。 -/
def pdCoefficientAt (a b : ℕ) :
    ((KA).X a).X b →ₛₗ[algebraMap A B] ((KB).X a).X b := by
  exact pdFormsCoefficientMap p A B r ⦋a⦌ b

set_option backward.isDefEq.respectTransparency false in
private def totalReductionSummand (n : ℕ) (ij : totalIndex n) :
    (pdDeRhamTotal p A r).X n →ₛₗ[algebraMap A B] (pdDeRhamTotal p B r).X n :=
  (insertAt KB n ij).hom.comp
    ((pdCoefficientAt p A B r ij.1.1 ij.1.2).comp (componentAt KA n ij).hom)

/-- 総次数ごとに各成分を同時に係数変換する。 -/
def pdTotalCoefficientMap (n : ℕ) :
    (pdDeRhamTotal p A r).X n →ₛₗ[algebraMap A B] (pdDeRhamTotal p B r).X n :=
  ∑ ij : totalIndex n, totalReductionSummand p A B r n ij

set_option backward.isDefEq.respectTransparency false in
/-- 総複体の係数変換の成分は、成分ごとの係数変換で与えられる。 -/
theorem pdTotalCoefficientMap_component (n : ℕ) (ij : totalIndex n)
    (x : (pdDeRhamTotal p A r).X n) :
    componentAt KB n ij (pdTotalCoefficientMap p A B r n x) =
      pdCoefficientAt p A B r ij.1.1 ij.1.2 (componentAt KA n ij x) := by
  classical
  simp only [pdTotalCoefficientMap, LinearMap.sum_apply, map_sum]
  change (∑ st : totalIndex n, componentAt KB n ij
    (totalReductionSummand p A B r n st x)) = _
  rw [Finset.sum_eq_single ij]
  · have e := ConcreteCategory.congr_hom (insertAt_componentAt_eq KB ij)
      (pdCoefficientAt p A B r ij.1.1 ij.1.2 (componentAt KA n ij x))
    exact e
  · intro st _ hst
    exact ConcreteCategory.congr_hom (insertAt_componentAt_ne KB st ij hst) _
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- 係数変換と一成分の挿入は可換。 -/
theorem pdTotalCoefficientMap_insert (n : ℕ) (ij : totalIndex n) (x : ((KA).X ij.1.1).X ij.1.2) :
    pdTotalCoefficientMap p A B r n (insertAt KA n ij x) =
      insertAt KB n ij (pdCoefficientAt p A B r ij.1.1 ij.1.2 x) := by
  apply sub_eq_zero.mp
  apply totalComponent_ext_zero KB
  intro a b hab
  let ab : totalIndex n := ⟨(a,b),hab⟩
  change componentAt KB n ab (_ - _) = 0
  rw [map_sub, sub_eq_zero, pdTotalCoefficientMap_component]
  by_cases he : ij = ab
  · subst ij
    have hA := ConcreteCategory.congr_hom (insertAt_componentAt_eq KA ab) x
    have hB := ConcreteCategory.congr_hom (insertAt_componentAt_eq KB ab)
      (pdCoefficientAt p A B r ab.1.1 ab.1.2 x)
    simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hA hB
    rw [hA, hB]
  · have hA := ConcreteCategory.congr_hom (insertAt_componentAt_ne KA ij ab he) x
    have hB := ConcreteCategory.congr_hom (insertAt_componentAt_ne KB ij ab he)
      (pdCoefficientAt p A B r ij.1.1 ij.1.2 x)
    simp only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hA hB
    rw [hA, hB, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem pdHorizontal_coefficients (i j : ℕ) (x : ((KA).X i).X j) :
    pdCoefficientAt p A B r (i+1) j (((KA).d i (i+1)).f j x) =
      ((KB).d i (i+1)).f j (pdCoefficientAt p A B r i j x) := by
  change ↑((pdRow p A r j).obj ⦋i⦌) at x
  change pdFormsCoefficientMap p A B r ⦋i+1⦌ j ((pdRowComplex p A r j).d i (i+1) x) =
    (pdRowComplex p B r j).d i (i+1) (pdFormsCoefficientMap p A B r ⦋i⦌ j x)
  simp only [pdRowComplex, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
    CochainComplex.of_d, AlternatingCofaceMapComplex.objD]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg ((-1 : ℤ)^t.val • ·)
    (pdFormsCoefficientMap_natural p A B r (SimplexCategory.δ t) j x)

set_option backward.isDefEq.respectTransparency false in
private theorem pdVertical_coefficients (i j : ℕ) (x : ((KA).X i).X j) :
    pdCoefficientAt p A B r i (j+1) (((KA).X i).d j (j+1) x) =
      ((KB).X i).d j (j+1) (pdFormsCoefficientMap p A B r ⦋i⦌ j x) := by
  change ↑((pdRow p A r j).obj ⦋i⦌) at x
  change pdFormsCoefficientMap p A B r ⦋i⦌ (j+1) ((pdDeRhamColumn p A r ⦋i⦌).d j (j+1) x) =
    (pdDeRhamColumn p B r ⦋i⦌).d j (j+1) (pdFormsCoefficientMap p A B r ⦋i⦌ j x)
  rw [column_d_eq, column_d_eq]
  exact pdFormsCoefficientMap_d p A B r ⦋i⦌ j x

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- 総複体の係数変換は総微分と可換。 -/
theorem pdTotalCoefficientMap_d (n : ℕ) (x : (pdDeRhamTotal p A r).X n) :
    pdTotalCoefficientMap p A B r (n+1) ((pdDeRhamTotal p A r).d n (n+1) x) =
      (pdDeRhamTotal p B r).d n (n+1) (pdTotalCoefficientMap p A B r n x) := by
  let F := pdTotalCoefficientMap p A B r
  let y := F (n+1) ((pdDeRhamTotal p A r).d n (n+1) x)
  let z := (pdDeRhamTotal p B r).d n (n+1) (F n x)
  suffices h : y - z = 0 from sub_eq_zero.mp h
  apply totalComponent_ext_zero KB
  intro i j hij
  rw [map_sub, sub_eq_zero]
  rcases i with _ | a <;> rcases j with _ | b
  · omega
  · have hn : n = b := by omega
    subst n
    change componentAt KB (b+1) ⟨(0,b+1),_⟩ (F (b+1) (((KA).total _).d b (b+1) x)) =
      componentAt KB (b+1) ⟨(0,b+1),_⟩ (((KB).total _).d b (b+1) (F b x))
    rw [pdTotalCoefficientMap_component]
    have hA := ConcreteCategory.congr_hom (totalD_component_zeroLeft KA b) x
    have hB := ConcreteCategory.congr_hom (totalD_component_zeroLeft KB b) (F b x)
    simp only [ConcreteCategory.comp_apply] at hA hB
    rw [hA, hB, pdTotalCoefficientMap_component, pdVertical_coefficients]
    rfl
  · have hn : n = a := by omega
    subst n
    change componentAt KB (a+1) ⟨(a+1,0),_⟩ (F (a+1) (((KA).total _).d a (a+1) x)) =
      componentAt KB (a+1) ⟨(a+1,0),_⟩ (((KB).total _).d a (a+1) (F a x))
    rw [pdTotalCoefficientMap_component]
    have hA := ConcreteCategory.congr_hom (totalD_component_zeroRight KA a) x
    have hB := ConcreteCategory.congr_hom (totalD_component_zeroRight KB a) (F a x)
    simp only [ConcreteCategory.comp_apply] at hA hB
    rw [hA, hB, pdTotalCoefficientMap_component, pdHorizontal_coefficients]
  · change componentAt KB (n+1) ⟨(a+1,b+1),_⟩ (F (n+1) (((KA).total _).d n (n+1) x)) =
      componentAt KB (n+1) ⟨(a+1,b+1),_⟩ (((KB).total _).d n (n+1) (F n x))
    rw [pdTotalCoefficientMap_component]
    have hA := ConcreteCategory.congr_hom (totalD_component_succ KA a b n (by omega)) x
    have hB := ConcreteCategory.congr_hom (totalD_component_succ KB a b n (by omega)) (F n x)
    simp only [ConcreteCategory.comp_apply, ModuleCat.hom_add, ModuleCat.hom_zsmul,
      LinearMap.add_apply, LinearMap.smul_apply] at hA hB
    rw [hA, hB, map_add, map_zsmul, pdHorizontal_coefficients, pdVertical_coefficients,
      pdTotalCoefficientMap_component, pdTotalCoefficientMap_component]
    rfl

end SerrePositivity.BhattScholze.Prismatic
