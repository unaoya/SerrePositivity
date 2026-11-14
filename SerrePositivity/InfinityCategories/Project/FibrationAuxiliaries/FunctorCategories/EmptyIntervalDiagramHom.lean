module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.EmptySimplicialDomain
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：空の定義域上の二図式の、実際の両端固定区間 Hom は終対象。
方針：空の定義域の関手空間を終対象とし、その中の区間族の一意性を使う。
規約：二つの元の図式の端点を厳密に固定する。
使われ方：空の境界の分類先 Hom と native Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 空の定義域上の関手空間は、全パラメーターの一意な族を持つ終対象。 -/
def functorSpace_isTerminal_of_isInitial {A X : SSet.{u}} (hA : IsInitial A) :
    IsTerminal ((ihom A).obj X) := by
  refine IsTerminal.ofUniqueHom (fun T ↦ curry ((hA.isInitialObj (tensorRight T)).to X)) ?_
  intro T f
  apply uncurry_injective
  exact (hA.isInitialObj (tensorRight T)).hom_ext _ _

/-- 終対象の二つの指定頂点の間の実際の区間 Hom も終対象。 -/
def intervalMappingSpace_isTerminal_of_isTerminal {X : SSet.{u}}
    (hX : IsTerminal X) (x y : X _⦋0⦌) : IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) := by
  refine IsTerminal.ofUniqueHom (fun T ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints
    (hX.from ((Δ[1] : SSet.{u}) ⊗ T)) (hX.hom_ext _ _) (hX.hom_ext _ _)) ?_
  intro T f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  exact hX.hom_ext _ _

/-- 空の定義域上の元の二図式間の、同じ両端固定区間 Hom は終対象。 -/
def intervalDiagramHom_isTerminal_of_isInitial {A X : SSet.{u}}
    (F G : A ⟶ X) (hA : IsInitial A) :
    IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :=
  intervalMappingSpace_isTerminal_of_isTerminal (functorSpace_isTerminal_of_isInitial hA) _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
