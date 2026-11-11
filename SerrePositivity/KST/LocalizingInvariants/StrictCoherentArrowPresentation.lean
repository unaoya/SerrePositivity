module

public import SerrePositivity.KST.LocalizingInvariants.StrictCoherentArrowTriangles
public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalHomotopy
public import SerrePositivity.KST.LocalizingInvariants.TriangleEdgeNormalization
public import SerrePositivity.KST.LocalizingInvariants.HomotopyMapTransport
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PrismHomotopy

/-!
概要：通常の自然変換の一つの射への制限を、元の二つの合成三角形の全 h Fun 合成で表す。
方針：元の正方形の対角分解に二単体の計算を渡し、自然性で共通対角の端点を揃える。
規約：自然変換の元の円柱を保持。使われ方：模型 cube の三因子の右辺表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.StrictArrow

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {F G : I ⥤ C} (η : F ⟶ G) {i j : I} (k : i ⟶ j)

def homotopy := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (shape k)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _))

lemma homotopy_map : (homotopy η k).h = prism η k := by
  change (shape k ▷ (Δ[1] : SSet.{max u v})) ≫
    (β_ _ Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η = _
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc]
  rfl

def post := TriangleEdge.normalizedPost (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (F.map k) (η.app j)).simplex
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map k)).edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map k ≫ η.app j)).edge
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (F.map k) (η.app j)).d₂
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (F.map k) (η.app j)).d₁

def pre := HomotopyArrow.rebase
  (TriangleEdge.normalizedPre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (η.app i) (G.map k)).simplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app i ≫ G.map k)).edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (G.map k)).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (η.app i) (G.map k)).d₁
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (η.app i) (G.map k)).d₀)
  (congrArg (fun r ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).edge) (η.naturality k).symm) rfl

lemma afterBottom_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SquareDiagonal.afterBottom (homotopy η k)))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (post η k))) := by
  apply HomotopyArrow.congr
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (homotopy η k).h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (F.map k) (η.app j)).simplex := by
    exact (congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ r) (homotopy_map η k)).trans
      (SSet.yonedaEquiv.eq_symm_apply.mpr (lower η k))
  change SquareDiagonal.postShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (homotopy η k).h = _
  rw [ht]
  rfl

lemma beforeTop_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SquareDiagonal.beforeTop (homotopy η k)))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (pre η k))) := by
  apply HomotopyArrow.congr
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (homotopy η k).h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (η.app i) (G.map k)).simplex := by
    exact (congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ r) (homotopy_map η k)).trans
      (SSet.yonedaEquiv.eq_symm_apply.mpr (upper η k))
  change _ = (HomotopyArrow.rebase _ _ _).h
  rw [HomotopyArrow.rebase_map]
  change SquareDiagonal.preShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (homotopy η k).h = _
  rw [ht]
  rfl

lemma presentation :
    Arrow.mk (homPre (shape k) (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap η)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _))))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (post η k)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (pre η k))) := by
  unfold homPre
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp]
  change Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (homotopy η k))) = _
  rw [SquareDiagonal.homMk_decomposition]
  exact arrow_mk_comp_congr (afterBottom_arrow η k) (beforeTop_arrow η k)

end SerrePositivity.KST.LocalizingInvariants.StrictArrow
