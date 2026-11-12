module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Δᵒᵖ の射列から標準単体への先頭頂点写像

## 概要
Δᵒᵖ の n 本の射列に対し、各途中の零頂点を最初の標準単体へ戻して n 単体を作る。

## 方針
単体作用素は順序を保つ。零頂点の最小性と射列の合成則から頂点列の単調性を示す。

## 規約
射列の最初の対象は変えない。任意の添字の引き戻しに対する同じ比較射を保持する。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。bar の射列で添字づけた実現比較の具体的な単体作用素。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization

/-- 各途中の単体の零頂点を、射列の最初の単体へ戻した頂点。 -/
def sourceVertex {n : ℕ} (s : ComposableArrows SimplexCategoryᵒᵖ n) (i : Fin (n + 1)) :
    Fin ((s.obj 0).unop.len + 1) :=
  (s.map (homOfLE (Fin.zero_le i))).unop.toOrderHom 0

/-- 零頂点を戻して得た頂点列は順序を保つ。 -/
theorem sourceVertex_monotone {n : ℕ} (s : ComposableArrows SimplexCategoryᵒᵖ n) :
    Monotone (sourceVertex s) := by
  intro i j hij
  have hc : s.map (homOfLE (Fin.zero_le j)) =
      s.map (homOfLE (Fin.zero_le i)) ≫ s.map (homOfLE hij) := by
    rw [← s.map_comp]
    rfl
  dsimp [sourceVertex]
  rw [hc]
  change (s.map (homOfLE (Fin.zero_le i))).unop.toOrderHom 0 ≤
    (s.map (homOfLE (Fin.zero_le i))).unop.toOrderHom
      ((s.map (homOfLE hij)).unop.toOrderHom 0)
  exact (s.map (homOfLE (Fin.zero_le i))).unop.toOrderHom.monotone (Fin.zero_le _)

/-- 同じ頂点列を持つ、標準 n 単体から最初の単体への単体作用素。 -/
def sourceVertexSimplex {n : ℕ} (s : ComposableArrows SimplexCategoryᵒᵖ n) :
    SimplexCategory.mk n ⟶ (s.obj 0).unop :=
  SimplexCategory.Hom.mk ⟨sourceVertex s, sourceVertex_monotone s⟩

/-- 射列の先頭の頂点は、元の標準単体の零頂点。 -/
theorem sourceVertex_zero {n : ℕ} (s : ComposableArrows SimplexCategoryᵒᵖ n) :
    sourceVertex s 0 = 0 := by
  simp [sourceVertex]

/-- 任意の添字作用素で引き戻した頂点は、先頭の比較射を通して元の同じ頂点になる。 -/
theorem sourceVertex_whisker {m n : ℕ} (s : ComposableArrows SimplexCategoryᵒᵖ n)
    (r : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (i : Fin (m + 1)) :
    (s.map (homOfLE (Fin.zero_le (r.toOrderHom 0)))).unop.toOrderHom
      (sourceVertex ((SimplexCategory.toCat.map r).toFunctor ⋙ s) i) =
        sourceVertex s (r.toOrderHom i) := by
  let α : Fin (m + 1) ⥤ Fin (n + 1) := (SimplexCategory.toCat.map r).toFunctor
  have hc : s.map (homOfLE (Fin.zero_le (α.obj 0))) ≫
      s.map (α.map (homOfLE (Fin.zero_le i))) =
      s.map (homOfLE (Fin.zero_le (α.obj i))) := by
    rw [← s.map_comp]
    rfl
  exact congrArg (fun f => f.unop.toOrderHom 0) hc

/-- 全単体作用素に自然な、射列と先頭の標準単体の比較。 -/
theorem sourceVertexSimplex_whisker {m n : ℕ}
    (s : ComposableArrows SimplexCategoryᵒᵖ n)
    (r : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    sourceVertexSimplex ((SimplexCategory.toCat.map r).toFunctor ⋙ s) ≫
      (s.map (homOfLE (Fin.zero_le (r.toOrderHom 0)))).unop =
        r ≫ sourceVertexSimplex s := by
  ext i : 3
  exact sourceVertex_whisker s r i

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
