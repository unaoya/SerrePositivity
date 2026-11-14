module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

/-!
概要：宇宙持ち上げのホモトピー圏から元のホモトピー圏への下降を関手として作る。
方針：頂点・辺・合成二単体の下降をホモトピー圏の生成表示へ渡す。
規約：指定射の類を保持。使われ方：小宇宙へ降ろす指定比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 宇宙持ち上げのホモトピー圏の下降関手。 -/
def universeHomotopyDown (X : SSet.{u}) :
    ((SSet.uliftFunctor.{v, u}).obj X).HomotopyCategory ⥤ X.HomotopyCategory :=
  Truncated.HomotopyCategory.lift (fun x => HomotopyCategory.mk x.down)
    (fun e => Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge e))
    (fun x => by rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge_id, Truncated.HomotopyCategory.homMk_id]; rfl)
    (fun t => Truncated.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedCompStruct t))

/-- 下降関手は元の実辺の下降の類を与える。 -/
lemma universeHomotopyDown_map_homMk {X : SSet.{u}}
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x y) :
    (universeHomotopyDown X).map (Truncated.HomotopyCategory.homMk e) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge e) := by
  unfold universeHomotopyDown
  apply Truncated.HomotopyCategory.lift_map_homMk
  intro x₀ x₁ x₂ e₀₁ e₁₂ e₀₂ t
  exact Truncated.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedCompStruct t)

/-- 既存の実頂点同型の下降は同じ指定射の類に対する関手の作用。 -/
lemma downVertexIso_eq_mapIso {X : SSet.{u}} [Quasicategory X]
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso e = (universeHomotopyDown X).mapIso e := by
  let a := Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y e.hom)
  have ha := Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y e.hom)
  apply Iso.ext
  change Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge a) =
    (universeHomotopyDown X).map e.hom
  rw [← ha, universeHomotopyDown_map_homMk]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
