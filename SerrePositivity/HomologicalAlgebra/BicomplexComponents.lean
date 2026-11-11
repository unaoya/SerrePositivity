module

public import SerrePositivity.HomologicalAlgebra.BicomplexProjection
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
# 第一象限の総複体の成分表示

## 概要
総次数を固定し、各二重次数への射影と微分の成分公式を与える。

## 方針
有限個の成分の挿入と射影を使う。

## 規約
二重次数は横、縦の順。

## 使われ方
行と列の完全性から総複体の比較を示す。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity.HomologicalAlgebra

variable {R : Type u} [CommRing R]

local notation "up" => ComplexShape.up ℕ

variable (K : HomologicalComplex₂ (ModuleCat.{u} R) up up) [K.HasTotal up]

/-- 指定した二重次数の成分を取り出す。 -/
def totalComponent (a b : ℕ) :
    (K.total up).X (a+b) ⟶ (K.X a).X b :=
  K.totalDesc fun i j h => if hi : i = a then eqToHom (by
    change i + j = a + b at h
    subst i
    have hj : j = b := Nat.add_left_cancel h
    subst j
    rfl) else 0

@[simp, reassoc]
theorem ιTotal_totalComponent (a b : ℕ) :
    K.ιTotal up a b (a+b) rfl ≫ totalComponent K a b = 𝟙 _ := by
  simp [totalComponent]

@[reassoc]
theorem ιTotal_totalComponent_of_ne {i j a b : ℕ} (h : i+j = a+b) (hne : i ≠ a) :
    K.ιTotal up i j (a+b) h ≫ totalComponent K a b = 0 := by
  simp [totalComponent, hne]

/-- 一つの総次数に含まれる二重次数。 -/
abbrev totalIndex (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}

instance totalIndexFintype (n : ℕ) : Fintype (totalIndex n) :=
  Fintype.ofEquiv (Fin (n+1)) {
    toFun i := ⟨(i, n-i), by omega⟩
    invFun x := ⟨x.1.1, by have h := x.2; omega⟩
    left_inv i := Fin.ext rfl
    right_inv x := by
      obtain ⟨⟨i,j⟩, h⟩ := x
      change i + j = n at h
      apply Subtype.ext
      exact Prod.ext rfl (by change n-i = j; omega) }

/-- 証明付きの総次数の添字で成分を取り出す。 -/
def componentAt (n : ℕ) (ij : totalIndex n) :
    (K.total up).X n ⟶ (K.X ij.1.1).X ij.1.2 :=
  eqToHom (congrArg (K.total up).X ij.2.symm) ≫ totalComponent K ij.1.1 ij.1.2

/-- 証明付きの総次数の添字で成分を挿入する。 -/
def insertAt (n : ℕ) (ij : totalIndex n) :
    (K.X ij.1.1).X ij.1.2 ⟶ (K.total up).X n :=
  K.ιTotal up ij.1.1 ij.1.2 n ij.2

@[simp, reassoc]
theorem insertAt_componentAt_eq {n : ℕ} (ij : totalIndex n) :
    insertAt K n ij ≫ componentAt K n ij = 𝟙 _ := by
  obtain ⟨⟨i,j⟩, h⟩ := ij
  change i+j = n at h
  subst n
  simp [insertAt, componentAt]

@[reassoc]
theorem insertAt_componentAt_ne {n : ℕ} (ij st : totalIndex n) (h : ij ≠ st) :
    insertAt K n ij ≫ componentAt K n st = 0 := by
  obtain ⟨⟨i,j⟩, hij⟩ := ij
  obtain ⟨⟨a,b⟩, hab⟩ := st
  change a+b = n at hab
  change i+j = n at hij
  subst n
  have hne : i ≠ a := by
    intro hia
    subst i
    have h' : j = b := Nat.add_left_cancel hij
    subst j
    exact h rfl
  simp [insertAt, componentAt, ιTotal_totalComponent_of_ne K hij hne]

private theorem total_component_decomposition (n : ℕ) :
    (∑ ij : totalIndex n, componentAt K n ij ≫ insertAt K n ij) = 𝟙 _ := by
  classical
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  let ab : totalIndex n := ⟨(a,b),h⟩
  change insertAt K n ab ≫ _ = _
  rw [Preadditive.comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single ab]
  · rw [← Category.assoc, insertAt_componentAt_eq, Category.id_comp]
    rfl
  · intro cd _ hcd
    rw [← Category.assoc, insertAt_componentAt_ne K ab cd hcd.symm, zero_comp]
  · simp

/-- 総複体の元は全成分が零なら零。 -/
theorem totalComponent_ext_zero {n : ℕ} (x : (K.total up).X n)
    (hx : ∀ a b (h : a+b = n), componentAt K n ⟨(a,b),h⟩ x = 0) :
    x = 0 := by
  have h := ConcreteCategory.congr_hom (total_component_decomposition K n) x
  change (∑ ij : totalIndex n, componentAt K n ij ≫ insertAt K n ij).hom x = x at h
  rw [ModuleCat.hom_sum, LinearMap.sum_apply] at h
  rw [← h]
  apply Finset.sum_eq_zero
  rintro ⟨⟨a,b⟩, hab⟩ _
  change insertAt K n _ (componentAt K n ⟨(a,b),hab⟩ x) = 0
  rw [hx, map_zero]

private theorem insertAt_componentAt {n : ℕ} (ij st : totalIndex n) :
    insertAt K n ij ≫ componentAt K n st =
      if h : ij = st then eqToHom (congrArg (fun t : totalIndex n => (K.X t.1.1).X t.1.2) h)
        else 0 := by
  classical
  split_ifs with h
  · subst st
    exact insertAt_componentAt_eq K ij
  · exact insertAt_componentAt_ne K ij st h

/-- 総微分の正の二重次数での成分は二つの隣接成分から求まる。 -/
theorem totalD_component_succ (a b n : ℕ) (h : a + b + 1 = n) :
    (K.total up).d n (n+1) ≫ componentAt K (n+1) ⟨(a+1,b+1), by omega⟩ =
      componentAt K n ⟨(a,b+1), by omega⟩ ≫ (K.d a (a+1)).f (b+1) +
      (-1 : ℤ)^(a+1) •
        (componentAt K n ⟨(a+1,b), by omega⟩ ≫ (K.X (a+1)).d b (b+1)) := by
  classical
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j = n at hij
  let ij : totalIndex n := ⟨(i,j),hij⟩
  rw [← Category.assoc, total_d_summand, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, Category.assoc, Preadditive.comp_add, Preadditive.comp_zsmul,
    ← Category.assoc, ← Category.assoc]
  have hi : i+1+j = n+1 := by omega
  have hj : i+(j+1) = n+1 := by omega
  let ab : totalIndex (n+1) := ⟨(a+1,b+1), by omega⟩
  let ab₀ : totalIndex n := ⟨(a,b+1), by omega⟩
  let ab₁ : totalIndex n := ⟨(a+1,b), by omega⟩
  change (K.d i (i+1)).f j ≫
      (insertAt K (n+1) ⟨(i+1,j),hi⟩ ≫ componentAt K (n+1) ab) +
    (-1 : ℤ)^i • ((K.X i).d j (j+1) ≫
      (insertAt K (n+1) ⟨(i,j+1),hj⟩ ≫ componentAt K (n+1) ab)) =
    (insertAt K n ij ≫ componentAt K n ab₀) ≫ (K.d a (a+1)).f (b+1) +
    (-1 : ℤ)^(a+1) • ((insertAt K n ij ≫ componentAt K n ab₁) ≫
      (K.X (a+1)).d b (b+1))
  simp only [insertAt_componentAt, ij, ab, ab₀, ab₁, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases ia : i = a
  · subst i
    have ej : j = b+1 := by omega
    subst j
    simp
  · by_cases ia' : i = a+1
    · subst i
      have ej : j = b := by omega
      subst j
      simp
    · simp [ia, ia']

/-- 横次数零での総微分は縦の微分だけ。 -/
theorem totalD_component_zeroLeft (b : ℕ) :
    (K.total up).d b (b+1) ≫ componentAt K (b+1) ⟨(0,b+1), Nat.zero_add _⟩ =
      componentAt K b ⟨(0,b), Nat.zero_add _⟩ ≫ (K.X 0).d b (b+1) := by
  classical
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j = b at hij
  let ij : totalIndex b := ⟨(i,j),hij⟩
  rw [← Category.assoc, total_d_summand, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, Category.assoc, ← Category.assoc]
  let c : totalIndex (b+1) := ⟨(0,b+1), Nat.zero_add _⟩
  let c₀ : totalIndex b := ⟨(0,b), Nat.zero_add _⟩
  change (K.d i (i+1)).f j ≫
      (insertAt K (b+1) ⟨(i+1,j),by omega⟩ ≫ componentAt K (b+1) c) +
    (-1 : ℤ)^i • ((K.X i).d j (j+1) ≫
      (insertAt K (b+1) ⟨(i,j+1),by omega⟩ ≫ componentAt K (b+1) c)) =
    (insertAt K b ij ≫ componentAt K b c₀) ≫ (K.X 0).d b (b+1)
  simp only [insertAt_componentAt, ij, c, c₀, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases hi : i = 0
  · subst i
    have hj : j = b := by omega
    subst j
    simp
  · simp [hi]

/-- 縦次数零での総微分は横の微分だけ。 -/
theorem totalD_component_zeroRight (a : ℕ) :
    (K.total up).d a (a+1) ≫ componentAt K (a+1) ⟨(a+1,0), Nat.add_zero _⟩ =
      componentAt K a ⟨(a,0), Nat.add_zero _⟩ ≫ (K.d a (a+1)).f 0 := by
  classical
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j = a at hij
  let ij : totalIndex a := ⟨(i,j),hij⟩
  rw [← Category.assoc, total_d_summand, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, Category.assoc, ← Category.assoc]
  let c : totalIndex (a+1) := ⟨(a+1,0), Nat.add_zero _⟩
  let c₀ : totalIndex a := ⟨(a,0), Nat.add_zero _⟩
  change (K.d i (i+1)).f j ≫
      (insertAt K (a+1) ⟨(i+1,j),by omega⟩ ≫ componentAt K (a+1) c) +
    (-1 : ℤ)^i • ((K.X i).d j (j+1) ≫
      (insertAt K (a+1) ⟨(i,j+1),by omega⟩ ≫ componentAt K (a+1) c)) =
    (insertAt K a ij ≫ componentAt K a c₀) ≫ (K.d a (a+1)).f 0
  simp only [insertAt_componentAt, ij, c, c₀, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases hj : j = 0
  · subst j
    have hi : i = a := by omega
    subst i
    simp
  · simp [hj]

/-- 一成分を挿入して総微分を取ると、二つの隣接成分に分かれる。 -/
theorem insertAt_total_d {n a b : ℕ} (h : a+b = n) :
    insertAt K n ⟨(a,b), h⟩ ≫ (K.total up).d n (n+1) =
      (K.d a (a+1)).f b ≫ insertAt K (n+1) ⟨(a+1,b), by omega⟩ +
      (-1 : ℤ)^a • ((K.X a).d b (b+1) ≫ insertAt K (n+1) ⟨(a,b+1), by omega⟩) :=
  total_d_summand K a b n h

/-- 指定した成分の横微分を取り出す。 -/
theorem insertAt_total_d_component_horizontal {n a b : ℕ} (h : a+b = n) :
    insertAt K n ⟨(a,b), h⟩ ≫ (K.total up).d n (n+1) ≫
      componentAt K (n+1) ⟨(a+1,b), by omega⟩ = (K.d a (a+1)).f b := by
  rw [← Category.assoc, insertAt_total_d, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, Category.assoc, insertAt_componentAt_eq, Category.comp_id]
  have hne : (⟨(a,b+1), by omega⟩ : totalIndex (n+1)) ≠ ⟨(a+1,b), by omega⟩ := by
    intro h'
    have hh := congrArg (fun x : totalIndex (n+1) => x.1.1) h'
    dsimp at hh
    omega
  rw [insertAt_componentAt_ne K _ _ hne, comp_zero, smul_zero, add_zero]

/-- 挿入した成分より小さい縦次数の成分は、総微分の後も零。 -/
theorem insertAt_total_d_component_lower {n a b i j : ℕ} (h : a+b = n)
    (hij : i+j = n+1) (hj : j < b) :
    insertAt K n ⟨(a,b), h⟩ ≫ (K.total up).d n (n+1) ≫
      componentAt K (n+1) ⟨(i,j), hij⟩ = 0 := by
  rw [← Category.assoc, insertAt_total_d, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, Category.assoc]
  have neq₁ : (⟨(a+1,b), by omega⟩ : totalIndex (n+1)) ≠ ⟨(i,j), hij⟩ := by
    intro he
    have := congrArg (fun x : totalIndex (n+1) => x.1.2) he
    dsimp at this
    omega
  have neq₂ : (⟨(a,b+1), by omega⟩ : totalIndex (n+1)) ≠ ⟨(i,j), hij⟩ := by
    intro he
    have := congrArg (fun x : totalIndex (n+1) => x.1.2) he
    dsimp at this
    omega
  rw [insertAt_componentAt_ne K _ _ neq₁, insertAt_componentAt_ne K _ _ neq₂]
  simp

end SerrePositivity.HomologicalAlgebra
