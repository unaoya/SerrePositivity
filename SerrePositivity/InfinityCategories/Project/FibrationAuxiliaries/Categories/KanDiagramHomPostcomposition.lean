module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictDiagramOppositeHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramUniversalEnriched
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison

/-!
概要：元の strict Kan 変換の全単体を、表現可能 Hom 図式の後合成へ移す。
方針：各成分で豊穣合成を curry し、元の変換の厳密な自然性を使う。
規約：元の全 Hom の Kan 性は要求しない。
使われ方：左切断 prism の終点を、実際の weighted Hom 作用と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories


/-- 各対象の変換を、同じ対象での表現可能 Hom の後合成へ写す。 -/
def kanDiagramHomPostcompositionComponent {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : I) :
    SimplicialCategory.sHom (F.val.obj i) (G.val.obj i) ⟶
      (ihom (SimplicialCategory.sHom x (F.val.obj i))).obj
        (SimplicialCategory.sHom x (G.val.obj i)) :=
  curry (eComp SSet x (F.val.obj i) (G.val.obj i))

private lemma kanHomPostcomposition_condition {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {d : SimplexCategoryᵒᵖ}
    (θ : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).obj d) {i j : I} (f : i ⟶ j)
    (k : SimplexCategoryᵒᵖ) (α : d ⟶ k) (a : (SimplicialCategory.sHom x (F.val.obj i)).obj k) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x).map f).app k
      (((kanDiagramHomPostcompositionComponent F G x i).app d (θ.val i)).app k α a) =
    ((kanDiagramHomPostcompositionComponent F G x j).app d (θ.val j)).app k α
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x).map f).app k a) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro l β
  apply ConcreteCategory.hom_ext
  intro z
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (G.val.map f)).app l
      ((θ.val i).app l _ (a.app l _ z)) =
    (θ.val j).app l _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (F.val.map f)).app l (a.app l _ z))
  simpa using θ.property f l (α ≫ β) (a.app l β z)

/-- 元の strict な変換の各単体は、表現可能 Hom 図式間の同じ次数の変換を与える。 -/
def kanDiagramHomPostcompositionSimplex {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {d : SimplexCategoryᵒᵖ}
    (θ : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).obj d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x) d :=
  ⟨fun i => (kanDiagramHomPostcompositionComponent F G x i).app d (θ.val i),
    fun f k α a => by exact kanHomPostcomposition_condition F G x θ f k α a⟩

/-- 全 Hom の後合成を、表現可能 Hom 図式の変換空間への単体集合の射へ束ねる。 -/
def kanDiagramHomPostcomposition {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x) where
  app d := ↾fun θ => ⟨fun i =>
    (kanDiagramHomPostcompositionComponent F G x i).app d (θ.val i),
    fun f k α a => by exact kanHomPostcomposition_condition F G x θ f k α a⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext i
    exact congrArg (fun f => f (θ.val i))
      ((kanDiagramHomPostcompositionComponent F G x i).naturality α)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
