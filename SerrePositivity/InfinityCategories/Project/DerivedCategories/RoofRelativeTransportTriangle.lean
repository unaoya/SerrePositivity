module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeFirstTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofFirstTriangleCollapse
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyPrecomposition

/-! # 境界固定比較を指定輸送に沿って動かす相対三角形

概要：境界固定の比較と同じ始端を持つ輸送を、部分係数上の退化三角形を保って充填する。
方針：始点を重ねた底三角形に沿い、左ファイブレーションの相対外ホーンを充填する。
規約：比較と指定輸送、全境界、底への射影を厳密に保つ。使われ方：実屋根の充填の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K L E B : SSet.{u}} (p : E ⟶ B) (j : K ⟶ L)
variable {f₀ f₁ g : L ⟶ E} (C : SSet.Homotopy f₀ f₁) (T : SSet.Homotopy f₀ g)

/-- 比較・指定輸送・部分係数の退化三角形と全射影を保持する充填。 -/
structure RoofRelativeTransportTriangle where
  family : L ⊗ Δ[2] ⟶ E
  first : (L ◁ (SSet.stdSimplex.δ (2 : Fin 3))) ≫ family = C.h
  diagonal : (L ◁ (SSet.stdSimplex.δ (1 : Fin 3))) ≫ family = T.h
  boundary : (j ▷ Δ[2]) ≫ family =
    (K ◁ (SSet.stdSimplex.σ (0 : Fin 2))) ≫ (j ▷ Δ[1]) ≫ T.h
  over : family ≫ p = (L ◁ (SSet.stdSimplex.σ (0 : Fin 2))) ≫ T.h ≫ p

/-- 左ファイブレーションの上で、境界固定比較を指定輸送へ相対的に延長する。 -/
lemma roofRelativeTransportTriangle_nonempty [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [Mono j]
    (hC : (j ▷ Δ[1]) ≫ C.h = fst K Δ[1] ≫ j ≫ f₀)
    (hCp : C.h ≫ p = fst L Δ[1] ≫ f₀ ≫ p) :
    Nonempty (RoofRelativeTransportTriangle p j C T) := by
  let U := (K ◁ (SSet.stdSimplex.σ (0 : Fin 2))) ≫ (j ▷ Δ[1]) ≫ T.h
  let b := (L ◁ (SSet.stdSimplex.σ (0 : Fin 2))) ≫ T.h ≫ p
  have hzero : (L ◁ (SSet.stdSimplex.δ (1 : Fin 2))) ≫ C.h =
      (L ◁ (SSet.stdSimplex.δ (1 : Fin 2))) ≫ T.h := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.fst_stdSimplexZero_comp_ι₀, Category.assoc, Category.assoc, C.h₀, T.h₀]
  have hf : (j ▷ Δ[1]) ≫ C.h = (K ◁ (SSet.stdSimplex.δ (2 : Fin 3))) ≫ U := by
    dsimp only [U]
    rw [← Category.assoc, ← whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangleCollapse_edge01,
      whiskerLeft_comp, Category.assoc]
    exact hC.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofIntervalReset_zero (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp j T)).symm
  have hg : (j ▷ Δ[1]) ≫ T.h = (K ◁ (SSet.stdSimplex.δ (1 : Fin 3))) ≫ U := by
    dsimp only [U]
    rw [← Category.assoc, ← whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangleCollapse_edge02,
      whiskerLeft_id, Category.id_comp]
  have hfp : C.h ≫ p = (L ◁ (SSet.stdSimplex.δ (2 : Fin 3))) ≫ b := by
    dsimp only [b]
    rw [← Category.assoc, ← whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangleCollapse_edge01,
      whiskerLeft_comp, Category.assoc]
    exact hCp.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ p) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofIntervalReset_zero T)).symm)
  have hgp : T.h ≫ p = (L ◁ (SSet.stdSimplex.δ (1 : Fin 3))) ≫ b := by
    dsimp only [b]
    rw [← Category.assoc, ← whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangleCollapse_edge02,
      whiskerLeft_id, Category.id_comp]
  have hUp : U ≫ p = (j ▷ Δ[2]) ≫ b := by
    dsimp only [U, b]
    rw [Category.assoc, ← whisker_exchange_assoc]
    rfl
  obtain ⟨W, hW₁, hW₂, hWb, hWp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofLeftFibration_relativeFirstTriangle p j C.h T.h hzero U b hf hg hfp hgp hUp
  exact ⟨⟨W, hW₁, hW₂, hWb, hWp⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
