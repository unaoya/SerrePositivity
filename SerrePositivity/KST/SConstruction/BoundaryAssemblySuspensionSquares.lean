module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblySuspensionPrisms

/-! # 元の四辺と合成列を保持する suspension 自然性 square
概要：元の段の射と固定構造射を四辺に持つ square と、合成・恒等との整合性。
方針：同じ全体円柱の一次元・二次元の制限を使い、全辺を厳密に計算する。
規約：square や合成の証人を各射で独立に選び直さない。
使われ方：BF 列の厳密化へ渡す指定した自然性と高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance boundarySuspensionSquares_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 全体円柱から得る、元の固定構造射の自然性 square。 -/
def boundaryAssemblyOriginalSuspensionSquare {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ SimplicialNerve PointedSimplicialSet.{u} :=
  boundaryAssemblyOriginalSuspensionPrism r F (nerve.edgeMk f).edge

/-- 下辺は元の段の入力射の suspension の辺そのもの。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_zero {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    SSet.ι₀ ≫ boundaryAssemblyOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (PointedSimplicialSet.circle.{u} ◁
          (boundaryKanRealizationFunctor r).map (F.map f))).edge := by
  rw [boundaryAssemblyOriginalSuspensionSquare, boundaryAssemblyOriginalSuspensionPrism_zero,
    ← Category.assoc, SSet.yonedaEquiv_symm_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge (F ⋙ boundaryKanRealizationFunctor r) f,
    SSet.yonedaEquiv_symm_comp, enrichedNerveMap_edge, suspensionEnrichedUnderlying_map]
  rfl

/-- 上辺は元の次段の入力射の辺そのもの。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_one {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    SSet.ι₁ ≫ boundaryAssemblyOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        ((boundaryKanRealizationFunctor (r + 1)).map (F.map f))).edge := by
  rw [boundaryAssemblyOriginalSuspensionSquare, boundaryAssemblyOriginalSuspensionPrism_one,
    SSet.yonedaEquiv_symm_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge (F ⋙ boundaryKanRealizationFunctor (r + 1)) f]
  rfl

/-- 左辺は入力の始点での元の固定構造射の辺そのもの。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_left {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ boundaryAssemblyOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (boundaryKanAssemblySigma r (F.obj i))).edge :=
  boundaryAssemblyOriginalSuspensionPrism_vertex r F (nerve.edgeMk f).edge
    (SSet.stdSimplex.obj₀Equiv.symm 0)

/-- 右辺は入力の終点での元の固定構造射の辺そのもの。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_right {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ boundaryAssemblyOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (boundaryKanAssemblySigma r (F.obj j))).edge :=
  boundaryAssemblyOriginalSuspensionPrism_vertex r F (nerve.edgeMk f).edge
    (SSet.stdSimplex.obj₀Equiv.symm 1)

/-- 合成列の prism の第一の側面は、元の第一の射の square。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_comp_first {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      boundaryAssemblyOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g) =
        boundaryAssemblyOriginalSuspensionSquare r F f := by
  have h := boundaryAssemblyOriginalSuspensionPrism_naturality r F
    (SimplexCategory.δ (2 : Fin 3)) (ComposableArrows.mk₂ f g)
  change (SSet.stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    boundaryAssemblyOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g) =
      boundaryAssemblyOriginalSuspensionPrism r F ((nerve I).δ 2 (ComposableArrows.mk₂ f g)) at h
  rw [nerve.δ₂_mk₂_eq] at h
  exact h

/-- 合成列の prism の第二の側面は、元の第二の射の square。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_comp_second {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      boundaryAssemblyOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g) =
        boundaryAssemblyOriginalSuspensionSquare r F g := by
  have h := boundaryAssemblyOriginalSuspensionPrism_naturality r F
    (SimplexCategory.δ (0 : Fin 3)) (ComposableArrows.mk₂ f g)
  change (SSet.stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    boundaryAssemblyOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g) =
      boundaryAssemblyOriginalSuspensionPrism r F ((nerve I).δ 0 (ComposableArrows.mk₂ f g)) at h
  rw [nerve.δ₀_mk₂_eq] at h
  exact h

/-- 合成列の prism の中央の側面は、元の合成射の square。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_comp_composite {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      boundaryAssemblyOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g) =
        boundaryAssemblyOriginalSuspensionSquare r F (f ≫ g) := by
  have h := boundaryAssemblyOriginalSuspensionPrism_naturality r F
    (SimplexCategory.δ (1 : Fin 3)) (ComposableArrows.mk₂ f g)
  change (SSet.stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    boundaryAssemblyOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g) =
      boundaryAssemblyOriginalSuspensionPrism r F ((nerve I).δ 1 (ComposableArrows.mk₂ f g)) at h
  rw [nerve.δ₁_mk₂_eq] at h
  exact h

/-- 恒等射の square は、元の対象での prism の退化そのもの。 -/
lemma boundaryAssemblyOriginalSuspensionSquare_id {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (SSet.stdSimplex.σ (0 : Fin 1) ▷ (Δ[1] : SSet.{u + 1})) ≫
      boundaryAssemblyOriginalSuspensionPrism r F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) =
        boundaryAssemblyOriginalSuspensionSquare r F (𝟙 i) := by
  have h := boundaryAssemblyOriginalSuspensionPrism_naturality r F
    (SimplexCategory.σ (0 : Fin 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
  change (SSet.stdSimplex.σ (0 : Fin 1) ▷ (Δ[1] : SSet.{u + 1})) ≫
    boundaryAssemblyOriginalSuspensionPrism r F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) =
      boundaryAssemblyOriginalSuspensionPrism r F ((nerve I).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) at h
  exact h.trans (congrArg (boundaryAssemblyOriginalSuspensionPrism r F)
    (nerve.σ₀_mk₀_eq i))

end SerrePositivity.KST.SConstruction
