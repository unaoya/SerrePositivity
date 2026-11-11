module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjunctionOppositeCounit
/-!
概要：標準区間条件から作る随伴の余単位を、元の指定ホモトピーの類へ回収する。
方針：全パラメータ Hom 対応の恒等射と、反対側の指定単位の回収を使う。
規約：元の h Fun の射を等式で保持する。使われ方：実 RHom 随伴の余単位の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalClosed Bicategory SSet
open scoped _root_.Simplicial

/-- 標準区間条件で得た随伴の余単位は、指定した同じ実ホモトピーの類。 -/
lemma qcatAdjunctionOfCounitIntervalCondition_counitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated))) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfCounitIntervalCondition H h).counitHom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (G ≫ F) (𝟙 Y)).injective
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfCounitIntervalCondition
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfOpposite_counitHom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition_unitHom]
  rfl
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
