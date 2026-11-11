module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaUnitRepresentative

/-!
概要：coherent な普遍 comma 切断の単位に、始対象条件を戻す。
方針：同じ標的の二重 fiber 内で矢印の Hom 類を比較し、頂点同型で始対象性を移す。
規約：代表の厳密な一致を仮定しない。使われ方：普遍矢印から随伴の構成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 各成分が comma の始対象である切断から作る単位は、始対象条件を満たす。 -/
lemma commaSectionUnit_initialCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = 𝟙 X)
    (h : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionFiberVertex G s hs x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionUnit G s hs) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff _).mpr
  intro x
  let η := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionUnit G s hs
  let v := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionTargetFiberVertex G s hs x
  let w := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η x
  have hh : Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x ((s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G).app (Opposite.op ⦋0⦌) x)
        v).toTruncated = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x ((s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G).app (Opposite.op ⦋0⦌) x)
        w).toTruncated := by
    dsimp only [v]
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionTargetFiberArrow_eq, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionUnit_component]
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberArrow_hom η x).symm
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaTargetFiber_isInitial_iff_of_homMk_eq G x _ v w hh).mp (h x)

/-- 相対始対象切断の同じ円柱の単位は、選び直した代表でも comma の普遍矢印。 -/
lemma commaSectionUnit_initialCondition_of_relativeInitial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = 𝟙 X)
    (h : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G)
      (s.app (Opposite.op ⦋0⦌) x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionUnit G s hs) :=
  commaSectionUnit_initialCondition G s hs fun x ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting.isInitialVertex_fiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionFiberVertex G s hs x) (h x)

/-- 各 comma の始対象から、一つの coherent な関手と始対象条件を持つ単位が存在。 -/
lemma exists_unit_initialCondition_of_fiberInitial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) :
    ∃ (F : X ⟶ Y) (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η := by
  obtain ⟨s, hs, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_unitCommaSection_of_fiberInitial G h
  exact ⟨s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionUnit G s hs,
    commaSectionUnit_initialCondition_of_relativeInitial G s hs hi⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
