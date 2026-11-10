module

public import SerrePositivity.HomologicalAlgebra.CochainProduct
public import SerrePositivity.HomologicalAlgebra.BicomplexComponents
import all SerrePositivity.HomologicalAlgebra.BicomplexComponents

/-!
# 双複体の総複体の積の微分

## 概要
双次数での Leibniz 則を総複体の積へ移す。

## 方針
挿入した双次数の成分で横微分と縦微分の公式を足し合わせる。

## 規約
総複体の次数の変換は添字の算術から得る。

## 使われ方
pd de Rham の二つの射影のコホモロジー積。
-/

public noncomputable section

open CategoryTheory SerrePositivity.HomologicalAlgebra

universe u

namespace SerrePositivity.HomologicalAlgebra

variable {R : Type u} [CommRing R]
local notation "up" => ComplexShape.up ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) up up) [K.HasTotal up]
local notation "T" => K.total up

private theorem total_cast_insert {i i' a a' b b' : ℕ}
    (ha : a = a') (hb : b = b') (h : i = i') (h₀ : a+b=i) (h₁ : a'+b'=i')
    (x : ((K).X a).X b) :
    cast (congrArg (fun n => ((T).X n : Type u)) h) (insertAt K i ⟨(a,b),h₀⟩ x) =
      insertAt K i' ⟨(a',b'),h₁⟩
        (cast (congrArg (fun n => (((K).X a').X n : Type u)) hb)
          (cast (congrArg (fun n => (((K).X n).X b : Type u)) ha) x)) := by
  subst a' b' i'
  rfl

private theorem insertAt_total_d_apply {i a b : ℕ} (h : a+b=i) (x : ((K).X a).X b) :
    (T).d i (i+1) (insertAt K i ⟨(a,b),h⟩ x) =
      insertAt K (i+1) ⟨(a+1,b),by omega⟩ (((K).d a (a+1)).f b x) +
      (-1 : ℤ)^a • insertAt K (i+1) ⟨(a,b+1),by omega⟩ (((K).X a).d b (b+1) x) :=
  ConcreteCategory.congr_hom (insertAt_total_d K h) x

private theorem total_cast_add {i j : ℕ} (h : i = j) (x y : (T).X i) :
    cast (congrArg (fun n => ((T).X n : Type u)) h) (x+y) =
      cast (congrArg (fun n => ((T).X n : Type u)) h) x +
        cast (congrArg (fun n => ((T).X n : Type u)) h) y := by
  subst j
  rfl

private theorem total_cast_zsmul {i j : ℕ} (h : i = j) (m : ℤ) (x : (T).X i) :
    cast (congrArg (fun n => ((T).X n : Type u)) h) (m • x) =
      m • cast (congrArg (fun n => ((T).X n : Type u)) h) x := by
  subst j
  rfl

omit [K.HasTotal up] in
private theorem component_cast_zsmul (a : ℕ) {i j : ℕ} (h : i = j)
    (m : ℤ) (x : (K.X a).X i) :
    cast (congrArg (fun n => ((K.X a).X n : Type u)) h) (m • x) =
      m • cast (congrArg (fun n => ((K.X a).X n : Type u)) h) x := by
  subst j
  rfl

variable
    (M : ∀ a b c d : ℕ, (K.X a).X b →ₗ[R] (K.X c).X d →ₗ[R] (K.X (a + c)).X (b + d))
    (mu : ∀ i j : ℕ, (K.total up).X i →ₗ[R] (K.total up).X j →ₗ[R] (K.total up).X (i + j))
    (hInsert : ∀ (i j : ℕ) (s : totalIndex i) (t : totalIndex j)
      (x : (K.X s.1.1).X s.1.2) (y : (K.X t.1.1).X t.1.2),
      mu i j (insertAt K i s x) (insertAt K j t y) =
        insertAt K (i+j) ⟨(s.1.1+t.1.1,s.1.2+t.1.2), by have := s.2; have := t.2; omega⟩
          (M s.1.1 s.1.2 t.1.1 t.1.2 x y))
    (hHorizontal : ∀ (a b c d : ℕ) (x : (K.X a).X b) (y : (K.X c).X d),
      (K.d (a+c) (a+c+1)).f (b+d) (M a b c d x y) =
        cast (congrArg (fun n => ((K.X n).X (b+d) : Type u)) (by omega : a+1+c = a+c+1))
          (M (a+1) b c d ((K.d a (a+1)).f b x) y) +
        (-1 : ℤ)^(a+b) • M a b (c+1) d x ((K.d c (c+1)).f d y))
    (hVertical : ∀ (a b c d : ℕ) (x : (K.X a).X b) (y : (K.X c).X d),
      (-1 : ℤ)^(a+c) • ((K.X (a+c)).d (b+d) (b+d+1) (M a b c d x y)) =
        cast (congrArg (fun n => ((K.X (a+c)).X n : Type u)) (by omega : b+1+d = b+d+1))
          ((-1 : ℤ)^a • M a (b+1) c d ((K.X a).d b (b+1) x) y) +
        (-1 : ℤ)^(a+b) • ((-1 : ℤ)^c • M a b c (d+1) x ((K.X c).d d (d+1) y)))

include hInsert hHorizontal hVertical in
set_option maxHeartbeats 1000000 in
-- 成分ごとに総微分を展開し、加法の添字を照合する。
set_option backward.isDefEq.respectTransparency false in
private theorem totalProduct_leibniz_insert (i j a b c d : ℕ) (hab : a+b=i) (hcd : c+d=j)
    (x : ((K).X a).X b) (y : ((K).X c).X d) :
    let x' := insertAt K i ⟨(a,b),hab⟩ x
    let y' := insertAt K j ⟨(c,d),hcd⟩ y
    (T).d (i+j) (i+j+1) (mu i j x' y') =
      cast (congrArg (fun n => ((T).X n : Type u)) (by omega : i+1+j = i+j+1))
        (mu (i+1) j ((T).d i (i+1) x') y') +
      (-1 : ℤ)^i • mu i (j+1) x' ((T).d j (j+1) y') := by
  dsimp only
  rw [hInsert, insertAt_total_d_apply, insertAt_total_d_apply, insertAt_total_d_apply]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hInsert, hInsert, hInsert, hInsert]
  rw [total_cast_add, total_cast_zsmul]
  dsimp only
  let ι : ((K).X (a+c)).X (b+d+1) ⟶ (T).X (i+j+1) :=
    insertAt K (i+j+1) ⟨(a+c,b+d+1),by omega⟩
  have hV := map_zsmul ι.hom ((-1 : ℤ)^(a+c))
    (((K).X (a+c)).d (b+d) (b+d+1) (M a b c d x y))
  erw [← hV, hHorizontal, hVertical]
  simp only [map_add, map_zsmul, smul_add]
  have hi : i+1+j = i+j+1 := by omega
  erw [total_cast_insert K (by omega : a+1+c = a+c+1) (rfl : b+d = b+d) hi
      (by omega) (by omega),
    total_cast_insert K (rfl : a+c = a+c) (by omega : b+1+d = b+d+1) hi (by omega) (by omega)]
  · erw [component_cast_zsmul K (a+c) (by omega : b+1+d = b+d+1), map_zsmul]
    simp only [cast_eq, hab]
    dsimp only [ι]
    rw [add_add_add_comm]
    rfl
  all_goals omega

private theorem total_cast_sum {i j : ℕ} (h : i = j) {α : Type*}
    (s : Finset α) (f : α → (T).X i) :
    cast (congrArg (fun n => ((T).X n : Type u)) h) (∑ a ∈ s, f a) =
      ∑ a ∈ s, cast (congrArg (fun n => ((T).X n : Type u)) h) (f a) := by
  subst j
  rfl

private theorem total_decomposition_apply {i : ℕ} (x : (T).X i) :
    ∑ a : totalIndex i, insertAt K i a (componentAt K i a x) = x := by
  have h := congrArg (fun f => (f : (T).X i ⟶ (T).X i).hom x)
    (total_component_decomposition K i)
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

include hInsert hHorizontal hVertical in
set_option maxHeartbeats 1000000 in
-- 二つの総次数の有限和と次数変換を展開する。
set_option backward.isDefEq.respectTransparency false in
/-- 双次数での Leibniz 則を総複体の積へ移す。 -/
theorem totalProduct_leibniz (i j : ℕ) (x : (T).X i) (y : (T).X j) :
    (T).d (i+j) (i+j+1) (mu i j x y) =
      cast (congrArg (fun n => ((T).X n : Type u)) (by omega : i+1+j = i+j+1))
        (mu (i+1) j ((T).d i (i+1) x) y) +
      (-1 : ℤ)^i • mu i (j+1) x ((T).d j (j+1) y) := by
  let f (a : totalIndex i) := insertAt K i a (componentAt K i a x)
  let g (b : totalIndex j) := insertAt K j b (componentAt K j b y)
  have hx : ∑ a, f a = x := total_decomposition_apply K x
  have hy : ∑ b, g b = y := total_decomposition_apply K y
  rw [← hx, ← hy]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  simp only [total_cast_sum K (by omega : i+1+j = i+j+1), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  obtain ⟨⟨a,b⟩, hab⟩ := s
  obtain ⟨⟨c,d⟩, hcd⟩ := t
  exact totalProduct_leibniz_insert K M mu hInsert hHorizontal hVertical i j a b c d hab hcd _ _

end SerrePositivity.HomologicalAlgebra
