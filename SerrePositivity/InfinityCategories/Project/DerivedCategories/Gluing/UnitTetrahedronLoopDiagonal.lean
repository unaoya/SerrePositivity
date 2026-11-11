module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTetrahedronRelativeComparison
/-! # 元実閉路の端から単位四面体の対角を回収する

概要：実左単位閉路の終端から、同じ四面体の終側標準面の対角を厳密に回収する。
方針：閉路の全正方形を時間1へ制限し、二つの標準面の交わりを照合する。
規約：対角の一致を追加仮定にせず、実閉路の端点則から得る。
使われ方：単位四面体比較からの左単位閉路の消去で、元係数対角を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingUnitTetrahedronLoop_diagonal {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (T : (Δ[3] : SSet.{u}) ⊗ K ⟶ Z) (U : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
    (h0 : (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ T = U)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h) :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b := by
  have hface : stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        stdSimplex.δ (0 : Fin 4) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitMissingFace_edge 0
  calc
    _ = ((stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) ▷ K) ≫ T := by
      rw [comp_whiskerRight, Category.assoc, h0]
    _ = (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T := by
      rw [← hface, comp_whiskerRight, Category.assoc]
    _ = (Δ[1] ◁ (ι₁ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫
        (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T := by
      rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily_one]
      simp only [Category.assoc]
    _ = (Δ[1] ◁ (ι₁ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h := by rw [ha]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, SSet.Homotopy.h₁]
lemma dgGluingUnitTetrahedronLoop_homMk_id_of_three_faces {K Z : SSet.{u}}
    [Quasicategory Z] {x y : Z _⦋0⦌}
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (T : (Δ[3] : SSet.{u}) ⊗ K ⟶ Z) (U : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
    (h0 : (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ T = U)
    (h1 : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ T = U)
    (h3 : (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ T =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ U)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTetrahedronLoop_homMk_id_of_unit_face T U h0 h1 h3 b l
    (dgGluingUnitTetrahedronLoop_diagonal b l T U h0 ha) ha
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
