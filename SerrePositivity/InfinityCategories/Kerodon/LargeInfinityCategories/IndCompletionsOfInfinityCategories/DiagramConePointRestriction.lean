module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeCommaInitial
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：元の Ind 図式の全錐 comma の点制限を、同じ元の評価頂点へ正規化する。
方針：Yoneda の点評価等式で終点の表示だけを変える。
規約：元の C への射影を保持。使われ方：元の射図式の始点余錐の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の小さい形状の指定点を、同じ持ち上げた形状の点として含める。 -/
def diagramShapePoint {K : SSet.{u}} (k : K _⦋0⦌) :
    (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K :=
  SSet.yonedaEquiv.symm (ULift.up k)

/-- 一点からのこの実包含は単射。 -/
instance diagramShapePoint_mono {K : SSet.{u}} (k : K _⦋0⦌) : Mono (diagramShapePoint k) :=
  ⟨fun f g _ => stdSimplex.isTerminalObj₀.hom_ext f g⟩

variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) (k : K _⦋0⦌)

/-- 元の図式の点制限の頂点は、同じ指定点の元の値そのもの。 -/
lemma diagramConePoint_value :
    SSet.yonedaEquiv (diagramShapePoint k ≫ D) =
      D.app (Opposite.op ⦋0⦌) (ULift.up k) := by
  rw [SSet.yonedaEquiv_comp, diagramShapePoint, Equiv.apply_symm_apply]

/-- 全錐の comma から、元の図式の同じ指定値への実 comma 制限。 -/
def diagramConePointRestriction :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeCommaPointRestriction κ D (diagramShapePoint k) ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)) (diagramConePoint_value κ D k))

/-- 元の始点図式は正規化した点制限でも厳密に保たれる。 -/
lemma diagramConePointRestriction_projection : diagramConePointRestriction κ D k ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D) := by
  rw [diagramConePointRestriction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftKanShapeTransport_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (diagramConePoint_value κ D k),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeCommaPointRestriction_projection]

/-- 始点包含が left anodyne なら、元の評価頂点への点制限は自明 Kan。 -/
lemma diagramConePointRestriction_trivialKanFibration
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (diagramShapePoint k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (diagramConePointRestriction κ D k) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indConeCommaPointRestriction_trivialKanFibration κ D
    (diagramShapePoint k) hi
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ h.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩

/-- 標準単体の元の最初の頂点は、持ち上げた形状でも left anodyne に含まれる。 -/
lemma diagramShapeFirstPoint_leftAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
      (diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin (n + 1)))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n
  have h : diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin (n + 1))) ≫ e.hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n : (Δ[0] : SSet.{u + 1}) ⟶ Δ[n]) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    rfl
  have he : diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin (n + 1))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ≫ e.inv := by
    rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.of_isIso _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
