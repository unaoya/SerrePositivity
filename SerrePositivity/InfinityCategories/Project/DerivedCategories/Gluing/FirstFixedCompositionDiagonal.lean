module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FirstFixedCompositionSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexFaceCurry

/-! 第一辺固定の全合成三角形の三辺と、同じ共通始終点を持つ対角評価。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSpace f z

lemma dgGluingFirstFixedCompositionEvaluation_first :
    (stdSimplex.δ (2 : Fin 3) ▷ E) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z =
      fst (Δ[1] : SSet.{u}) E ≫ SSet.yonedaEquiv.symm f.edge := by
  calc
    _ = (horn₂₁.ι₀₁ ▷ E) ≫ ((horn 2 1).ι ▷ E) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z := by
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation_horn,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap_first]

lemma dgGluingFirstFixedCompositionEvaluation_last :
    (stdSimplex.δ (0 : Fin 3) ▷ E) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) := by
  calc
    _ = (horn₂₁.ι₁₂ ▷ E) ≫ ((horn 2 1).ι ▷ E) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z := by
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation_horn,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap_last]

lemma dgGluingFirstFixedCompositionDiagonal_source :
    (stdSimplex.δ (1 : Fin 2) ▷ E) ≫ (stdSimplex.δ (1 : Fin 3) ▷ E) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z =
      fst (Δ[0] : SSet.{u}) E ≫ SSet.yonedaEquiv.symm x := by
  have hδ : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    dgGluingFirstFixedCompositionEvaluation_first, ← Category.assoc, whiskerRight_fst,
    Category.assoc, f.δ_one_yonedaEquiv_symm]

lemma dgGluingFirstFixedCompositionDiagonal_target :
    (stdSimplex.δ (0 : Fin 2) ▷ E) ≫ (stdSimplex.δ (1 : Fin 3) ▷ E) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z =
      fst (Δ[0] : SSet.{u}) E ≫ SSet.yonedaEquiv.symm z := by
  have hδ : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    dgGluingFirstFixedCompositionEvaluation_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_target]

def dgGluingFirstFixedCompositionDiagonal : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfVertexFaces
    ((stdSimplex.δ (1 : Fin 3) ▷ E) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z)
    (dgGluingFirstFixedCompositionDiagonal_source f z)
    (dgGluingFirstFixedCompositionDiagonal_target f z)

lemma dgGluingFirstFixedCompositionDiagonal_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingFirstFixedCompositionDiagonal f z) =
      (stdSimplex.δ (1 : Fin 3) ▷ E) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z := by
  unfold dgGluingFirstFixedCompositionDiagonal
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfVertexFaces_uncurry]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
