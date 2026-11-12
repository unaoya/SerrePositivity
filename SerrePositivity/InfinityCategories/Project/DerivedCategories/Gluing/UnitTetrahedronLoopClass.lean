module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTetrahedronRelativeFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTriangleRelativeLoopClass
/-! # 相対単位四面体比較による左単位対角閉路の消去

概要：同じ退化四面体への内角固定比較があれば、残る左単位面の実対角閉路の類は恒等射となる。
方針：第2面の三辺固定比較へ制限し、元閉路の四辺固定二次元比較を回収する。
規約：上流の比較の存在だけを隔離し、元四面体・元対角閉路・全入力を保持する。
使われ方：六片の左単位面を消去して六角形関係を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingUnitTetrahedronLoop_homMk_id {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (T : (Δ[3] : SSet.{u}) ⊗ K ⟶ Z) (U : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
    (H : SSet.Homotopy T ((stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U))
    (hH : (((horn 3 2).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst ((horn 3 2 : SSet.{u}) ⊗ K) Δ[1] ≫ ((horn 3 2).ι ▷ K) ≫
        (stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U)
    (hB : (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  have hg : (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b := by rw [hB]
  let N := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitMissingFaceRelativeHomotopy T U H) rfl hg
  have hN : N.h = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitMissingFaceRelativeHomotopy T U H).h := rfl
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoop_homMk_id b l ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T) N ha
  intro i
  rw [hN]
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitMissingFaceRelativeHomotopy_fixed T U H hH i
  simpa only [Category.assoc, hB] using hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
