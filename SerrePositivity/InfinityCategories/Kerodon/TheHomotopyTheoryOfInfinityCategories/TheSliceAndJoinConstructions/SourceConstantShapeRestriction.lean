module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.SourceConstantTransformationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostcompositionVertices

/-!
概要：定値始域からの変換を、図式の形状に沿って全族のまま制限する。
方針：区間写像空間の前合成と、その元の円柱の評価を用いる。
規約：指定頂点と任意のパラメータを保持し、充填性は仮定しない。
使われ方：元の錐の切断写像と実際の切断制限との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 定値始域の指定頂点を保持した、変換の全空間の形状制限。 -/
def sourceConstantShapeRestriction {A K X : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (z : X _⦋0⦌) :
    intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex F) ⟶
      intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex (i ≫ F)) :=
  intervalMappingPostOfEq ((pre i).app X)
    (functorVertex (SSet.const z)) (functorVertex F)
    (by rw [functorVertex_precomposition, SSet.comp_const])
    (functorVertex_precomposition i F)

/-- 制限した全変換の円柱は、元の円柱の同じ形状への制限そのもの。 -/
lemma sourceConstantShapeRestriction_prism {A K X T : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (z : X _⦋0⦌)
    (a : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex F)) :
    sourceConstantTransformationPrism (a ≫ sourceConstantShapeRestriction i F z) =
      (i ▷ (Δ[1] : SSet.{u}) ▷ T) ≫ sourceConstantTransformationPrism a := by
  rw [sourceConstantTransformationPrism, sourceConstantShapeRestriction,
    intervalMappingPostOfEq_uncurry, uncurry_pre_app, ← Category.assoc,
    ← associator_naturality_left, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
