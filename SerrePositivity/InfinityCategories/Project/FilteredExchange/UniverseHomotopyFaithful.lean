module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseHomotopyDown
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

/-!
概要：ホモトピー圏の宇宙下降が指定射の等式を反映することを証明する。
方針：辺と合成三角形を元の値のまま持ち上げ、下降後の持ち上げを恒等関手へ同定する。
規約：quasicategory 性は不要。使われ方：下降した指定 path の等式を元の宇宙へ反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の頂点・辺・合成三角形の持ち上げによるホモトピー圏の関手。 -/
def universeHomotopyUp (X : SSet.{u}) :
    X.HomotopyCategory ⥤ ((SSet.uliftFunctor.{v, u}).obj X).HomotopyCategory :=
  Truncated.HomotopyCategory.lift (fun x => HomotopyCategory.mk (ULift.up x))
    (fun e => Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge e))
    (fun x => by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge_id, Truncated.HomotopyCategory.homMk_id]; rfl)
    (fun t => Truncated.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedCompStruct t))

/-- 元の辺の射の類を、その同じ辺の持ち上げの類へ写す。 -/
lemma universeHomotopyUp_map_homMk {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (universeHomotopyUp.{u, v} X).map (Truncated.HomotopyCategory.homMk e) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge e) := by
  unfold universeHomotopyUp
  apply Truncated.HomotopyCategory.lift_map_homMk
  intro x₀ x₁ x₂ e₀₁ e₁₂ e₀₂ t
  exact Truncated.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedCompStruct t)

/-- 大きい実辺を下降して持ち上げ直すと、元の同じ辺になる。 -/
lemma uliftTruncatedEdge_down {X : SSet.{u}}
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge e) = e := by
  apply Truncated.Edge.ext
  rfl

/-- 下降して持ち上げ直す関手は、大きい元のホモトピー圏の恒等関手。 -/
lemma universeHomotopyDown_up (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.universeHomotopyDown.{u, v} X ⋙ universeHomotopyUp X = 𝟭 _ := by
  apply Truncated.HomotopyCategory.functor_ext
    (F := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.universeHomotopyDown.{u, v} X ⋙ universeHomotopyUp X)
    (G := 𝟭 _) (fun _ => rfl)
  intro x y e
  simp only [Functor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.universeHomotopyDown_map_homMk, universeHomotopyUp_map_homMk,
    uliftTruncatedEdge_down, Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 元のホモトピー圏への宇宙下降は、射の等式を反映する。 -/
lemma universeHomotopyDown_faithful (X : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.universeHomotopyDown.{u, v} X).Faithful :=
  (universeHomotopyDown_up.{u, v} X).faithful_of_comp

end SerrePositivity.InfinityCategories.Project.FilteredExchange
