module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgewiseRefinementVertex

/-!
概要：元の精密化を保持する共通解像の二辺の四面を、実際の共通頂点へ戻す。
方針：外側・内側の包含と二つの退化を有限順序の射として計算する。
規約：両辺の共通終点は元の一単体そのものを保持する頂点。
使われ方：左右区間比較の二自然性正方形の共通の成分の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 右解像の始点は元の始点に定値な一単体を表す共通解像の頂点。 -/
lemma edgewiseRefinementRightResolution_source {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X).δ 1 (edgewiseRefinementRightResolution e) =
      edgewiseRefinementVertex (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e) := by
  rw [edgewiseRefinementRightResolution, edgewiseRefinementStandard_face]
  have h : SimplexCategory.mkHom (edgewiseOneFaceInclusion 1) ≫
      (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 := by
    ext j
    fin_cases j <;> rfl
  rw [h]

/-- 右解像の終点は元の一単体そのものを表す共通解像の頂点。 -/
lemma edgewiseRefinementRightResolution_target {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X).δ 0 (edgewiseRefinementRightResolution e) =
      edgewiseRefinementVertex e := by
  rw [edgewiseRefinementRightResolution, edgewiseRefinementStandard_face]
  have h : SimplexCategory.mkHom (edgewiseOneFaceInclusion 0) ≫
      (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) = 𝟙 ⦋1⦌ := by
    ext j
    fin_cases j <;> rfl
  rw [h]
  simp

/-- 左解像の始点は元の終点に定値な一単体を表す共通解像の頂点。 -/
lemma edgewiseRefinementLeftResolution_source {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X).δ 1 (edgewiseRefinementLeftResolution e) =
      edgewiseRefinementVertex (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e) := by
  rw [edgewiseRefinementLeftResolution, edgewiseRefinementStandard_face]
  have h : SimplexCategory.mkHom (edgewiseOneFaceInclusion 1) ≫
      (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 := by
    ext j
    fin_cases j <;> rfl
  rw [h]

/-- 左解像の終点も元の同じ一単体を表す共通解像の頂点。 -/
lemma edgewiseRefinementLeftResolution_target {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X).δ 0 (edgewiseRefinementLeftResolution e) =
      edgewiseRefinementVertex e := by
  rw [edgewiseRefinementLeftResolution, edgewiseRefinementStandard_face]
  have h : SimplexCategory.mkHom (edgewiseOneFaceInclusion 0) ≫
      (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) = 𝟙 ⦋1⦌ := by
    ext j
    fin_cases j <;> rfl
  rw [h]
  simp

end SerrePositivity.InfinityCategories.F2
