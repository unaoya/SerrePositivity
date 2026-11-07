module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Alexander–Whitney 積の微分

## 概要
交代余面微分に関する Alexander–Whitney 積の Leibniz 則。

## 方針
余面を前面側と後面側に分け、共有頂点に対応する二項を相殺する。

## 規約
次数 m の左因子の後で微分すると符号は (−1)^m。

## 使われ方
余単体的可換環のコホモロジーの積と Bockstein。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable (X : CosimplicialObject CommRingCat.{u})

/-- 交代余面微分を元に作用させると、余面の値の交代和となる。 -/
theorem cochainDifferential_apply (n : ℕ) (x : X.obj ⦋n⦌) :
    cochainDifferential X n x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • X.map (SimplexCategory.δ i) x := by
  let Y : CosimplicialObject AddCommGrpCat.{u} := X ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  change (AddCommGrpCat.homAddEquiv (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Y.δ i)) x = _
  rw [map_sum]
  simp only [AddMonoidHom.finsetSum_apply, AddCommGrpCat.homAddEquiv_apply, AddCommGrpCat.hom_zsmul,
    AddMonoidHom.zsmul_apply]
  rfl

private theorem castObj {a b : ℕ} (h : a = b) (x : X.obj ⦋a⦌) :
    cast (congrArg (fun n => (X.obj ⦋n⦌ : Type u)) h) x =
      X.map (eqToHom (congrArg SimplexCategory.mk h)) x := by
  subst b
  simp

private theorem coface_val {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((SimplexCategory.δ i).toOrderHom j).val =
      if j.val < i.val then j.val else j.val + 1 := by
  change (i.succAbove j).val = _
  by_cases h : j.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt i j h, ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

private theorem front_val (m n : ℕ) (i : Fin (m + 1)) :
    ((frontFace m n).toOrderHom i).val = i.val :=
  rfl

private theorem back_val (m n : ℕ) (i : Fin (n + 1)) :
    ((backFace m n).toOrderHom i).val = m + i.val :=
  rfl

private theorem simplex_comp_apply {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (i : Fin (a.len + 1)) :
    (f ≫ g).toOrderHom i = g.toOrderHom (f.toOrderHom i) :=
  rfl

private theorem simplex_eqToHom_val {a b : SimplexCategory} (h : a = b) (i : Fin (a.len + 1)) :
    ((eqToHom h).toOrderHom i).val = i.val := by
  subst b
  simp

private theorem frontCofaceCup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌)
    (i : Fin (m + 1)) :
    X.map (SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (m + n + 2))) (cup X x y) =
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
        (cup X (X.map (SimplexCategory.δ i.castSucc) x) y) := by
  rw [castObj X (by omega : (m + 1) + n = m + n + 1)]
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
  simp only [cup, map_mul, ← CommRingCat.comp_apply, ← X.map_comp]
  erw [h₁, h₂]

private theorem backCofaceCup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌)
    (i : Fin (n + 1)) :
    X.map (SimplexCategory.δ (⟨m + i.val + 1, by omega⟩ : Fin (m + n + 2))) (cup X x y) =
      cup X x (X.map (SimplexCategory.δ i.succ) y) := by
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
  simp only [cup, map_mul, ← CommRingCat.comp_apply, ← X.map_comp]
  erw [h₁, h₂]

private theorem middleCofaceCup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) :
    cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
      (cup X (X.map (SimplexCategory.δ (Fin.last (m + 1))) x) y) =
        cup X x (X.map (SimplexCategory.δ (0 : Fin (n + 2))) y) := by
  rw [castObj X (by omega : (m + 1) + n = m + n + 1)]
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
  simp only [cup, map_mul, ← CommRingCat.comp_apply, ← X.map_comp]
  erw [h₁, h₂]

/-- 概要：余鎖の Alexander–Whitney 積は交代余面微分に関する Leibniz 則を満たす。
方針：前面側と後面側の余面を分け、共有頂点で現れる二項を打ち消す。
規約：左因子の次数 m に応じて右因子の微分に (−1)^m を掛ける。
使われ方：コホモロジーの cup 積と Bockstein の Leibniz 則。 -/
theorem cochainDifferential_cup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) :
    cochainDifferential X (m + n) (cup X x y) =
      cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
        (cup X (cochainDifferential X m x) y) +
      (-1 : ℤ) ^ m • cup X x (cochainDifferential X n y) := by
  let e : ⦋m + 1 + n⦌ ⟶ ⦋m + n + 1⦌ := eqToHom (congrArg SimplexCategory.mk (by omega))
  let left (i : Fin (m + 2)) : X.obj ⦋m + n + 1⦌ :=
    (-1 : ℤ) ^ i.val • X.map e (cup X (X.map (SimplexCategory.δ i) x) y)
  let right (i : Fin (n + 2)) : X.obj ⦋m + n + 1⦌ :=
    (-1 : ℤ) ^ (m + i.val) • cup X x (X.map (SimplexCategory.δ i) y)
  have hleft : cast (congrArg (fun k => (X.obj ⦋k⦌ : Type u))
        (by omega : (m + 1) + n = m + n + 1))
      (cup X (cochainDifferential X m x) y) = ∑ i, left i := by
    rw [castObj X (by omega : (m + 1) + n = m + n + 1), cochainDifferential_apply]
    simp only [left, cup, map_sum, map_mul, map_zsmul, Finset.sum_mul, smul_mul_assoc]
    rfl
  have hright : (-1 : ℤ) ^ m • cup X x (cochainDifferential X n y) = ∑ i, right i := by
    rw [cochainDifferential_apply]
    simp only [right, cup, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm, Finset.smul_sum,
      pow_add, mul_zsmul]
  rw [hleft, hright, Fin.sum_univ_castSucc left, Fin.sum_univ_succ right, cochainDifferential_apply]
  let term (i : Fin (m + n + 2)) : X.obj ⦋m + n + 1⦌ :=
    (-1 : ℤ) ^ i.val • X.map (SimplexCategory.δ i) (cup X x y)
  let indices : Fin ((m + 1) + (n + 1)) ≃ Fin (m + n + 2) := finCongr (by omega)
  have hsplit : ∑ i, term i = (∑ i : Fin (m + 1), left i.castSucc) +
      ∑ i : Fin (n + 1), right i.succ := by
    rw [← Equiv.sum_comp indices term, Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hd : indices (Fin.castAdd (n + 1) i) =
          (⟨i.val, by omega⟩ : Fin (m + n + 2)) := rfl
      change (-1 : ℤ) ^ i.val • X.map
        (SimplexCategory.δ (indices (Fin.castAdd (n + 1) i))) (cup X x y) = _
      rw [hd, frontCofaceCup X x y i, castObj X (by omega : (m + 1) + n = m + n + 1)]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      dsimp [term, right, indices]
      have h : (m + 1) + i.val = m + i.val + 1 := by omega
      have hd : indices (Fin.natAdd (m + 1) i) =
          (⟨m + i.val + 1, by omega⟩ : Fin (m + n + 2)) := Fin.ext h
      change (-1 : ℤ) ^ ((m + 1) + i.val) • X.map
        (SimplexCategory.δ (indices (Fin.natAdd (m + 1) i))) (cup X x y) = _
      rw [hd, backCofaceCup X x y i]
      exact congrArg
        (fun q : ℕ => (-1 : ℤ) ^ q • cup X x (X.map (SimplexCategory.δ i.succ) y))
        (by omega : (m + 1) + i.val = m + (i.val + 1))
  change (∑ i, term i) = _
  rw [hsplit]
  have hmiddle : left (Fin.last (m + 1)) = -right (0 : Fin (n + 2)) := by
    have h := middleCofaceCup X x y
    rw [castObj X (by omega : (m + 1) + n = m + n + 1)] at h
    change (-1 : ℤ) ^ (m + 1) • X.map e
        (cup X (X.map (SimplexCategory.δ (Fin.last (m + 1))) x) y) =
      -((-1 : ℤ) ^ (m + 0) • cup X x (X.map (SimplexCategory.δ (0 : Fin (n + 2))) y))
    rw [show X.map e (cup X (X.map (SimplexCategory.δ (Fin.last (m + 1))) x) y) =
      cup X x (X.map (SimplexCategory.δ (0 : Fin (n + 2))) y) from h]
    simp [pow_succ]
  rw [hmiddle]
  abel

end SerrePositivity.Cosimplicial
