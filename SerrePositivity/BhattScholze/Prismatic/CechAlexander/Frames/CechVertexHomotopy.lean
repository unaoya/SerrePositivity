module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy
public import Mathlib.CategoryTheory.Types.Basic
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra.FrameHelpers

/-!
# 頂点の変数で検査する Čech ホモトピー

## 概要
写像が各頂点の変数で決まる余単体的対象について、二つの変数像を切り替える
写像族からホモトピーを作る。

## 方針
各恒等式を頂点の添字と切り替え条件に帰着する。
対象の台集合を読む関手と、変数上での外延性だけを使う。

## 規約
第 0 項の変数像を各頂点の定値写像で移す。

## 使われ方
BS 著者版 Remark 4.19 の prismatic 枠の比較。
-/

public noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v w

namespace SerrePositivity.BhattScholze.Prismatic.CechVertexHomotopy

open PDCechNerve (val_succAbove val_predAbove)

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
variable {X Y : CosimplicialObject C} (f g : X ⟶ Y) {S : Type*}
variable (vars : ∀ n : ℕ, S → Fin (n + 1) → F.obj (X.obj ⦋n⦌))
variable (vars_map : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) x i,
  F.map (X.map θ) (vars m x i) = vars n x (θ.toOrderHom i))
variable (hom_ext : ∀ {n : ℕ} {T : C} {a b : X.obj ⦋n⦌ ⟶ T},
  (∀ x i, F.map a (vars n x i) = F.map b (vars n x i)) → a = b)

/-- 第 0 項の元を指定した頂点へ送る。 -/
def atVertex (n : ℕ) (i : Fin (n + 1)) (z : F.obj (Y.obj ⦋0⦌)) :
    F.obj (Y.obj ⦋n⦌) :=
  F.map (Y.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) z

private theorem atVertex_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) (z : F.obj (Y.obj ⦋0⦌)) :
    F.map (Y.map θ) (atVertex F (Y := Y) m i z) = atVertex F (Y := Y) n (θ.toOrderHom i) z := by
  unfold atVertex
  rw [← F.map_comp_apply, ← Y.map_comp, SimplexCategory.const_comp]

include vars_map in
private theorem app_vertex (a : X ⟶ Y) (n : ℕ) (x : S) (i : Fin (n + 1)) :
    F.map (a.app ⦋n⦌) (vars n x i) =
      atVertex F (Y := Y) n i (F.map (a.app ⦋0⦌) (vars 0 x 0)) := by
  let θ := SimplexCategory.const ⦋0⦌ ⦋n⦌ i
  have hv := vars_map θ x (0 : Fin 1)
  change F.map (X.map θ) (vars 0 x 0) = vars n x i at hv
  rw [← hv, ← F.map_comp_apply, a.naturality, F.map_comp_apply] <;> rfl

/-- 境目まで左の像を使い、それ以降は右の像を使う。 -/
def mixedValue {n : ℕ} (j : Fin (n + 1)) (x : S) (i : Fin (n + 2)) :
    F.obj (Y.obj ⦋n⦌) :=
  atVertex F (Y := Y) n (j.predAbove i)
    (if i ≤ j.castSucc then F.map (f.app ⦋0⦌) (vars 0 x 0)
      else F.map (g.app ⦋0⦌) (vars 0 x 0))

variable (H : ∀ {n : ℕ}, Fin (n + 1) → (X.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌))
variable (H_vars : ∀ {n : ℕ} (j : Fin (n + 1)) x i,
  F.map (H j) (vars (n + 1) x i) = mixedValue F f g vars j x i)

include vars_map hom_ext H_vars in
/-- 混合頂点の写像が与えられれば、交代和に移せる余単体ホモトピーが得られる。 -/
def ofMixedVertices :
    SimplicialObject.Homotopy
      ((cosimplicialSimplicialEquiv C).functor.map f.op)
      ((cosimplicialSimplicialEquiv C).functor.map g.op) where
  h j := (H j).op
  h_zero_comp_δ_zero n := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.δ 0) ≫ H 0 = g.app ⦋n⦌
    apply hom_ext
    intro x i
    rw [F.map_comp_apply, vars_map, H_vars, app_vertex F vars vars_map]
    change mixedValue F f g vars (0 : Fin (n + 1)) x ((0 : Fin (n + 2)).succAbove i) = _
    unfold mixedValue
    have hi : ¬ (0 : Fin (n + 2)).succAbove i ≤ (0 : Fin (n + 1)).castSucc := by
      change ¬ ((0 : Fin (n + 2)).succAbove i).val ≤ 0
      rw [val_succAbove]
      simp
    rw [ite_eq_right hi]
    exact congrArg (fun a => atVertex F (Y := Y) n a
      (F.map (g.app ⦋0⦌) (vars 0 x 0))) (Fin.predAbove_succAbove 0 i)
  h_last_comp_δ_last n := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.δ (Fin.last (n + 1))) ≫ H (Fin.last n) = f.app ⦋n⦌
    apply hom_ext
    intro x i
    rw [F.map_comp_apply, vars_map, H_vars, app_vertex F vars vars_map]
    change mixedValue F f g vars (Fin.last n) x ((Fin.last (n + 1)).succAbove i) = _
    unfold mixedValue
    have hi : (Fin.last (n + 1)).succAbove i ≤ (Fin.last n).castSucc := by
      have ht := i.isLt
      simp only [Fin.le_def, val_succAbove, Fin.val_last, Fin.val_castSucc, ite_eq_left ht]
      omega
    rw [ite_eq_left hi]
    apply congrArg (fun a => atVertex F (Y := Y) n a (F.map (f.app ⦋0⦌) (vars 0 x 0)))
    apply Fin.ext
    have ht := i.isLt
    simp only [val_succAbove, val_predAbove, Fin.val_last, ite_eq_left ht]
    split_ifs <;> omega
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.δ i.castSucc) ≫ H j.succ =
      H j ≫ Y.map (SimplexCategory.δ i)
    apply hom_ext
    intro x a
    simp only [F.map_comp_apply, vars_map, H_vars, mixedValue, atVertex_map]
    simp only [Fin.le_def, Fin.val_castSucc] at hij
    change atVertex F (Y := Y) _ (j.succ.predAbove (i.castSucc.succAbove a)) _ =
      atVertex F (Y := Y) _ (i.succAbove (j.predAbove a)) _
    congr 1
    · apply Fin.ext
      simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    · apply if_congr _ rfl rfl
      change i.castSucc.succAbove a ≤ j.succ.castSucc ↔ a ≤ j.castSucc
      simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
  h_succ_comp_δ_castSucc_succ j := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.δ j.castSucc.succ) ≫ H j.succ =
      X.map (SimplexCategory.δ j.castSucc.succ) ≫ H j.castSucc
    apply hom_ext
    intro x a
    simp only [F.map_comp_apply, vars_map, H_vars, mixedValue]
    change atVertex F (Y := Y) _ (j.succ.predAbove (j.castSucc.succ.succAbove a)) _ =
      atVertex F (Y := Y) _ (j.castSucc.predAbove (j.castSucc.succ.succAbove a)) _
    congr 1
    · apply Fin.ext
      simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    · apply if_congr _ rfl rfl
      change j.castSucc.succ.succAbove a ≤ j.succ.castSucc ↔
        j.castSucc.succ.succAbove a ≤ j.castSucc.castSucc
      simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.δ i.succ) ≫ H j.castSucc =
      H j ≫ Y.map (SimplexCategory.δ i)
    apply hom_ext
    intro x a
    simp only [F.map_comp_apply, vars_map, H_vars, mixedValue, atVertex_map]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    change atVertex F (Y := Y) _ (j.castSucc.predAbove (i.succ.succAbove a)) _ =
      atVertex F (Y := Y) _ (i.succAbove (j.predAbove a)) _
    congr 1
    · apply Fin.ext
      simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    · apply if_congr _ rfl rfl
      change i.succ.succAbove a ≤ j.castSucc.castSucc ↔ a ≤ j.castSucc
      simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
  h_comp_σ_castSucc_of_le i j hij := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.σ i.castSucc) ≫ H j =
      H j.succ ≫ Y.map (SimplexCategory.σ i)
    apply hom_ext
    intro x a
    simp only [F.map_comp_apply, vars_map, H_vars, mixedValue, atVertex_map]
    simp only [Fin.le_def] at hij
    change atVertex F (Y := Y) _ (j.predAbove (i.castSucc.predAbove a)) _ =
      atVertex F (Y := Y) _ (i.predAbove (j.succ.predAbove a)) _
    congr 1
    · apply Fin.ext
      simp only [val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    · apply if_congr _ rfl rfl
      change i.castSucc.predAbove a ≤ j.castSucc ↔ a ≤ j.succ.castSucc
      simp only [Fin.le_def, val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
  h_comp_σ_succ_of_lt i j hji := by
    apply Quiver.Hom.unop_inj
    change X.map (SimplexCategory.σ i.succ) ≫ H j =
      H j.castSucc ≫ Y.map (SimplexCategory.σ i)
    apply hom_ext
    intro x a
    simp only [F.map_comp_apply, vars_map, H_vars, mixedValue, atVertex_map]
    simp only [Fin.le_def] at hji
    change atVertex F (Y := Y) _ (j.predAbove (i.succ.predAbove a)) _ =
      atVertex F (Y := Y) _ (i.predAbove (j.castSucc.predAbove a)) _
    congr 1
    · apply Fin.ext
      simp only [val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    · apply if_congr _ rfl rfl
      change i.succ.predAbove a ≤ j.castSucc ↔ a ≤ j.castSucc.castSucc
      simp only [Fin.le_def, val_predAbove, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega

end SerrePositivity.BhattScholze.Prismatic.CechVertexHomotopy
