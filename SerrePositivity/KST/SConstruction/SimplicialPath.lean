module
public import SerrePositivity.CategoryTheory.Simplex.Prefix
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-! # 単体的対象の経路構成と追加退化
概要：先頭頂点を残す次数のずらしは零段への augmentation と追加退化を持つ。
方針：先頭頂点の包含と σ₀ を使い、単体恒等式を計算する。
規約：任意の値の圏に適用。使われ方：S 構成の delooping の経路対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open scoped Simplicial

/-- 概要：先頭頂点を追加した単体の先頭頂点の包含。
方針：[0] からの定数零写像を取る。
規約：全ての次数で先頭頂点。使われ方：経路構成の augmentation。 -/
def simplicialPathVertex (d : SimplexCategory) :
    ⦋0⦌ ⟶ SimplexPrefix.functor.obj d :=
  SimplexCategory.Hom.mk (OrderHom.const _ 0)

/-- 概要：零次元の先頭頂点の包含は δ₁。
方針：唯一の頂点の像を比較する。
規約：標準面の添字は一。使われ方：追加退化の augmentation の式。 -/
lemma simplicialPathVertex_zero : simplicialPathVertex ⦋0⦌ =
    SimplexCategory.δ (1 : Fin 2) := by
  ext i : 3
  have hi : (i : Fin 1) = 0 := @Subsingleton.elim (Fin 1) inferInstance i 0
  subst i
  rfl

/-- 概要：先頭頂点の包含は先頭追加関手について自然。
方針：先頭追加した全単体作用素が零を零へ送ることを使う。
規約：厳密等号。使われ方：経路構成の augmentation の自然性。 -/
lemma simplicialPathVertex_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    simplicialPathVertex d ≫ SimplexPrefix.functor.map f = simplicialPathVertex e := by
  ext i : 3
  rfl

/-- 概要：先頭頂点を残す単体的経路構成。
方針：先頭追加関手の反対で前合成する。
規約：第 n 段は X の第 n+1 段。使われ方：S 構成の経路対象。 -/
def simplicialPath {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    SimplicialObject C := SimplexPrefix.functor.op ⋙ X

/-- 概要：単体的経路構成から元の零段への augmentation。
方針：各次数で先頭頂点へ制限する。
規約：標的は元の零段の定数単体的対象。使われ方：追加退化による収縮。 -/
def simplicialPathAugmentation {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    simplicialPath X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (X.obj (Opposite.op ⦋0⦌)) where
  app d := X.map (simplicialPathVertex d.unop).op
  naturality {d e} f := by
    change X.map (SimplexPrefix.functor.map f.unop).op ≫
      X.map (simplicialPathVertex e.unop).op = X.map (simplicialPathVertex d.unop).op ≫ 𝟙 _
    rw [Category.comp_id, ← X.map_comp, ← op_comp, simplicialPathVertex_naturality]

/-- 概要：零段への augmentation を備えた経路構成。
方針：経路構成とその augmentation を comma 対象にまとめる。
規約：値の圏に極限は要求しない。使われ方：追加退化の構造の入力。 -/
def augmentedSimplicialPath {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    SimplicialObject.Augmented C where
  left := simplicialPath X
  right := X.obj (Opposite.op ⦋0⦌)
  hom := simplicialPathAugmentation X

/-- 概要：経路構成は先頭頂点の重複による追加退化を持つ。
方針：全次数の σ₀ と先頭追加の作用素の式を単体恒等式で照合する。
規約：元の対象の充填性は不要。使われ方：経路実現の収縮。 -/
def simplicialPathExtraDegeneracy {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedSimplicialPath X) where
  s' := X.σ (0 : Fin 1)
  s n := X.σ (0 : Fin (n + 2))
  s'_comp_ε := by
    change X.σ (0 : Fin 1) ≫ X.map (simplicialPathVertex ⦋0⦌).op = 𝟙 _
    rw [simplicialPathVertex_zero]
    exact X.δ_comp_σ_succ
  s₀_comp_δ₁ := by
    change X.σ (0 : Fin 2) ≫
      X.map (SimplexPrefix.functor.map (SimplexCategory.δ (1 : Fin 2))).op =
        X.map (simplicialPathVertex ⦋0⦌).op ≫ X.σ (0 : Fin 1)
    rw [SimplexPrefix.map_δ, simplicialPathVertex_zero]
    exact X.δ_comp_σ_of_gt (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide)
  s_comp_δ₀ n := by
    change X.σ (0 : Fin (n + 2)) ≫
      X.map (SimplexPrefix.functor.map (SimplexCategory.δ (0 : Fin (n + 2)))).op = 𝟙 _
    rw [SimplexPrefix.map_δ]
    exact X.δ_comp_σ_succ
  s_comp_δ n i := by
    change X.σ (0 : Fin (n + 3)) ≫
      X.map (SimplexPrefix.functor.map (SimplexCategory.δ i.succ)).op =
        X.map (SimplexPrefix.functor.map (SimplexCategory.δ i)).op ≫ X.σ (0 : Fin (n + 2))
    rw [SimplexPrefix.map_δ, SimplexPrefix.map_δ]
    exact X.δ_comp_σ_of_gt (i := i.succ) (j := (0 : Fin (n + 2))) (by simp)
  s_comp_σ n i := by
    change X.σ (0 : Fin (n + 2)) ≫
      X.map (SimplexPrefix.functor.map (SimplexCategory.σ i.succ)).op =
        X.map (SimplexPrefix.functor.map (SimplexCategory.σ i)).op ≫ X.σ (0 : Fin (n + 3))
    rw [SimplexPrefix.map_σ, SimplexPrefix.map_σ]
    exact (X.σ_comp_σ (i := (0 : Fin (n + 2))) (j := i.succ) (by simp)).symm

end SerrePositivity.KST.SConstruction
