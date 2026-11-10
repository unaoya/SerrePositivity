module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz
public import Mathlib.Algebra.Category.ModuleCat.Basic
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz

/-!
# Alexander–Whitney の双線形対

## 概要
三つの余単体的加群の自然な双線形対から、余鎖の積と横微分の Leibniz 則を得る。

## 方針
前面側と後面側の余面の恒等式を使い、共有頂点の二項を相殺する。

## 規約
符号は左の余単体次数で決める。

## 使われ方
pd de Rham 総複体の積。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.Cosimplicial

variable {R : Type u} [CommRing R]
variable (X Y Z : CosimplicialObject (ModuleCat.{u} R))
variable (μ : ∀ n, X.obj n →ₗ[R] Y.obj n →ₗ[R] Z.obj n)
variable (hμ : ∀ {a b} (θ : a ⟶ b) (x : X.obj a) (y : Y.obj a),
  Z.map θ (μ a x y) = μ b (X.map θ x) (Y.map θ y))

/-- 自然な双線形対の Alexander–Whitney 積。 -/
def awBilinear {m n : ℕ} (x : X.obj ⦋m⦌) (y : Y.obj ⦋n⦌) : Z.obj ⦋m + n⦌ :=
  μ ⦋m + n⦌ (X.map (frontFace m n) x) (Y.map (backFace m n) y)

/-- 余単体的加群の交代余面微分。 -/
def moduleCofaceDifferential (X : CosimplicialObject (ModuleCat.{u} R)) (n : ℕ) :
    X.obj ⦋n⦌ ⟶ X.obj ⦋n + 1⦌ :=
  AlternatingCofaceMapComplex.objD X n

private theorem moduleCofaceDifferential_apply (X : CosimplicialObject (ModuleCat.{u} R))
    (n : ℕ) (x : X.obj ⦋n⦌) :
    moduleCofaceDifferential X n x =
      ∑ i : Fin (n + 2), (-1 : ℤ)^i.val • X.map (SimplexCategory.δ i) x := by
  rw [moduleCofaceDifferential, AlternatingCofaceMapComplex.objD]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rfl

private theorem castModuleObj {a b : ℕ} (h : a = b) (x : Z.obj ⦋a⦌) :
    cast (congrArg (fun n => (Z.obj ⦋n⦌ : Type u)) h) x =
      Z.map (eqToHom (congrArg SimplexCategory.mk h)) x := by
  subst b
  simp

include hμ in
private theorem frontCofacePair {m n : ℕ} (x : X.obj ⦋m⦌) (y : Y.obj ⦋n⦌)
    (i : Fin (m + 1)) :
    Z.map (SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (m + n + 2))) (awBilinear X Y Z μ x y) =
      cast (congrArg (fun k => (Z.obj ⦋k⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
        (awBilinear X Y Z μ (X.map (SimplexCategory.δ i.castSucc) x) y) := by
  rw [castModuleObj Z (by omega : (m + 1) + n = m + n + 1)]
  let d := SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (m + n + 2))
  let e : ⦋m + 1 + n⦌ ⟶ ⦋m + n + 1⦌ := eqToHom (congrArg SimplexCategory.mk (by omega))
  have h₁ : frontFace m n ≫ d = (SimplexCategory.δ i.castSucc ≫ frontFace (m + 1) n) ≫ e := by
    ext j
    simp only [d, e, simplex_comp_apply, coface_val, front_val,
      simplex_eqToHom_val, Fin.val_castSucc]
    rfl
  have h₂ : backFace m n ≫ d = backFace (m + 1) n ≫ e := by
    ext j
    simp only [d, e, simplex_comp_apply, coface_val, back_val,
      simplex_eqToHom_val]
    have h : ¬ m + j.val < i.val := by omega
    erw [ite_eq_right h]
    omega
  simp only [awBilinear, hμ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  erw [h₁, h₂]

include hμ in
private theorem backCofacePair {m n : ℕ} (x : X.obj ⦋m⦌) (y : Y.obj ⦋n⦌)
    (i : Fin (n + 1)) :
    Z.map (SimplexCategory.δ (⟨m + i.val + 1, by omega⟩ : Fin (m + n + 2))) (awBilinear X Y Z μ x y) =
      awBilinear X Y Z μ x (Y.map (SimplexCategory.δ i.succ) y) := by
  let d := SimplexCategory.δ (⟨m + i.val + 1, by omega⟩ : Fin (m + n + 2))
  have h₁ : frontFace m n ≫ d = frontFace m (n + 1) := by
    ext j
    simp only [d, simplex_comp_apply, coface_val, front_val]
    have h : j.val < m + i.val + 1 := by
      have hj := j.isLt
      change j.val < m + 1 at hj
      omega
    erw [ite_eq_left h]
  have h₂ : backFace m n ≫ d = SimplexCategory.δ i.succ ≫ backFace m (n + 1) := by
    ext j
    simp only [d, simplex_comp_apply, coface_val, back_val, Fin.val_succ]
    by_cases h : j.val < i.val + 1
    · have h' : m + j.val < m + i.val + 1 := by omega
      erw [ite_eq_left h', ite_eq_left h]
    · have h' : ¬ m + j.val < m + i.val + 1 := by omega
      erw [ite_eq_right h', ite_eq_right h]
      omega
  simp only [awBilinear, hμ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  erw [h₁, h₂]
  rfl

include hμ in
private theorem middleCofacePair {m n : ℕ} (x : X.obj ⦋m⦌) (y : Y.obj ⦋n⦌) :
    cast (congrArg (fun k => (Z.obj ⦋k⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
      (awBilinear X Y Z μ (X.map (SimplexCategory.δ (Fin.last (m + 1))) x) y) =
        awBilinear X Y Z μ x (Y.map (SimplexCategory.δ (0 : Fin (n + 2))) y) := by
  rw [castModuleObj Z (by omega : (m + 1) + n = m + n + 1)]
  let e : ⦋m + 1 + n⦌ ⟶ ⦋m + n + 1⦌ := eqToHom (congrArg SimplexCategory.mk (by omega))
  have h₁ : (SimplexCategory.δ (Fin.last (m + 1)) ≫ frontFace (m + 1) n) ≫ e =
      frontFace m (n + 1) := by
    ext j
    simp only [e, simplex_comp_apply, simplex_eqToHom_val, front_val, coface_val, Fin.val_last]
    have h : j.val < m + 1 := j.isLt
    erw [ite_eq_left h]
  have h₂ : backFace (m + 1) n ≫ e =
      SimplexCategory.δ (0 : Fin (n + 2)) ≫ backFace m (n + 1) := by
    ext j
    simp only [e, simplex_comp_apply, simplex_eqToHom_val, back_val, coface_val, Fin.val_zero]
    erw [ite_eq_right (Nat.not_lt_zero _)]
    omega
  simp only [awBilinear, hμ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  erw [h₁, h₂]
  rfl

include hμ in
/-- Alexander–Whitney の双線形対の横微分に対する Leibniz 則。 -/
theorem moduleCofaceDifferential_awBilinear {m n : ℕ} (x : X.obj ⦋m⦌) (y : Y.obj ⦋n⦌) :
    moduleCofaceDifferential Z (m + n) (awBilinear X Y Z μ x y) =
      cast (congrArg (fun k => (Z.obj ⦋k⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
        (awBilinear X Y Z μ (moduleCofaceDifferential X m x) y) +
      (-1 : ℤ) ^ m • awBilinear X Y Z μ x (moduleCofaceDifferential Y n y) := by
  let e : ⦋m + 1 + n⦌ ⟶ ⦋m + n + 1⦌ := eqToHom (congrArg SimplexCategory.mk (by omega))
  let left (i : Fin (m + 2)) : Z.obj ⦋m + n + 1⦌ :=
    (-1 : ℤ) ^ i.val • Z.map e (awBilinear X Y Z μ (X.map (SimplexCategory.δ i) x) y)
  let right (i : Fin (n + 2)) : Z.obj ⦋m + n + 1⦌ :=
    (-1 : ℤ) ^ (m + i.val) • awBilinear X Y Z μ x (Y.map (SimplexCategory.δ i) y)
  have hleft : cast (congrArg (fun k => (Z.obj ⦋k⦌ : Type u))
        (by omega : (m + 1) + n = m + n + 1))
      (awBilinear X Y Z μ (moduleCofaceDifferential X m x) y) = ∑ i, left i := by
    rw [castModuleObj Z (by omega : (m + 1) + n = m + n + 1), moduleCofaceDifferential_apply]
    simp only [left, awBilinear, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  have hright : (-1 : ℤ) ^ m • awBilinear X Y Z μ x (moduleCofaceDifferential Y n y) = ∑ i, right i := by
    rw [moduleCofaceDifferential_apply]
    simp only [right, awBilinear, map_sum, map_zsmul, Finset.smul_sum,
      pow_add, mul_zsmul]
  rw [hleft, hright, Fin.sum_univ_castSucc left, Fin.sum_univ_succ right, moduleCofaceDifferential_apply]
  let term (i : Fin (m + n + 2)) : Z.obj ⦋m + n + 1⦌ :=
    (-1 : ℤ) ^ i.val • Z.map (SimplexCategory.δ i) (awBilinear X Y Z μ x y)
  let indices : Fin ((m + 1) + (n + 1)) ≃ Fin (m + n + 2) := finCongr (by omega)
  have hsplit : ∑ i, term i = (∑ i : Fin (m + 1), left i.castSucc) +
      ∑ i : Fin (n + 1), right i.succ := by
    rw [← Equiv.sum_comp indices term, Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hd : indices (Fin.castAdd (n + 1) i) =
          (⟨i.val, by omega⟩ : Fin (m + n + 2)) := rfl
      change (-1 : ℤ) ^ i.val • Z.map
        (SimplexCategory.δ (indices (Fin.castAdd (n + 1) i))) (awBilinear X Y Z μ x y) = _
      rw [hd, frontCofacePair X Y Z μ hμ x y i, castModuleObj Z (by omega : (m + 1) + n = m + n + 1)]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      dsimp [term, right, indices]
      have h : (m + 1) + i.val = m + i.val + 1 := by omega
      have hd : indices (Fin.natAdd (m + 1) i) =
          (⟨m + i.val + 1, by omega⟩ : Fin (m + n + 2)) := Fin.ext h
      change (-1 : ℤ) ^ ((m + 1) + i.val) • Z.map
        (SimplexCategory.δ (indices (Fin.natAdd (m + 1) i))) (awBilinear X Y Z μ x y) = _
      rw [hd, backCofacePair X Y Z μ hμ x y i]
      exact congrArg
        (fun q : ℕ => (-1 : ℤ) ^ q • awBilinear X Y Z μ x (Y.map (SimplexCategory.δ i.succ) y))
        (by omega : (m + 1) + i.val = m + (i.val + 1))
  change (∑ i, term i) = _
  rw [hsplit]
  have hmiddle : left (Fin.last (m + 1)) = -right (0 : Fin (n + 2)) := by
    have h := middleCofacePair X Y Z μ hμ x y
    rw [castModuleObj Z (by omega : (m + 1) + n = m + n + 1)] at h
    change (-1 : ℤ) ^ (m + 1) • Z.map e
        (awBilinear X Y Z μ (X.map (SimplexCategory.δ (Fin.last (m + 1))) x) y) =
      -((-1 : ℤ) ^ (m + 0) • awBilinear X Y Z μ x (Y.map (SimplexCategory.δ (0 : Fin (n + 2))) y))
    rw [show Z.map e (awBilinear X Y Z μ (X.map (SimplexCategory.δ (Fin.last (m + 1))) x) y) =
      awBilinear X Y Z μ x (Y.map (SimplexCategory.δ (0 : Fin (n + 2))) y) from h]
    simp [pow_succ]
  rw [hmiddle]
  abel


end SerrePositivity.Cosimplicial
