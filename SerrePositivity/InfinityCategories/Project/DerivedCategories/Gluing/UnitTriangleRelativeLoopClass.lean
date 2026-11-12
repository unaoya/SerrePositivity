module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTriangleRelativeLoopComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativeHomotopyEdgeClass
/-! # 相対単位三角形比較が与える対角閉路の零性

概要：退化単位三角形への三辺固定比較から、元対角閉路の関手圏の類が恒等射となることを得る。
方針：四辺固定の実比較を区間写像空間へ戻し、両端固定二変形の類を比較する。
規約：相対比較だけを明示入力とし、元閉路と全時間を保持する。
使われ方：選択済み四面体の左単位面を、六角形関係の中で消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K Z : SSet.{u}} {x y : Z _⦋0⦌}
  (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (l : SSet.Homotopy b b)
  (A : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
  (H : SSet.Homotopy A ((stdSimplex.σ (0 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b))
  (ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h)
  (hfaces : ∀ i : Fin 3, ((stdSimplex.δ i ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Δ[1] ⊗ K) Δ[1] ≫ (stdSimplex.δ i ▷ K) ≫
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b)

def dgGluingUnitTriangleLoopRelativeHomotopy :
    SSet.Homotopy l.h (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl b).h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy_source b l A H ha hfaces)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy_target b l A H ha hfaces)

include hfaces ha in
lemma dgGluingUnitTriangleLoop_homMk_refl :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl b)) := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha
  let hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy_source b l A H ha hfaces
  let hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy_target b l A H ha hfaces
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativeHomotopy_homMk_eq l (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl b)
    (dgGluingUnitTriangleLoopRelativeHomotopy b l A H ha hfaces)
  · have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse_fixed T hx hy (ι₀ : K ⟶ _)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy_zero_fixed b l A H ha hfaces)
    simpa only [dgGluingUnitTriangleLoopRelativeHomotopy, T, hx, hy,
      Category.assoc, SSet.Homotopy.h₀] using he
  · have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse_fixed T hx hy (ι₁ : K ⟶ _)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTriangleLoopUncurriedHomotopy_one_fixed b l A H ha hfaces)
    simpa only [dgGluingUnitTriangleLoopRelativeHomotopy, T, hx, hy,
      Category.assoc, SSet.Homotopy.h₁] using he

include hfaces ha in
lemma dgGluingUnitTriangleLoop_homMk_id :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  rw [dgGluingUnitTriangleLoop_homMk_refl b l A H ha hfaces,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
