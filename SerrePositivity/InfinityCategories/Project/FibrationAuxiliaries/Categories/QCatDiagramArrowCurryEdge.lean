module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramArrowCurry
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction

/-!
概要：元の自然変換の積上の図式を curry して得る辺は、同じ prism の元の辺。
方針：定値な図式パラメーターを全次数の区間と底で評価する。
規約：同じ一単体を保持し、成分ごとの一致で代用しない。
使われ方：既存の結合区間族と結合同型の分類像の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ積上の図式の curry は、元の射を因子交換して curry した頂点になる。 -/
lemma qCatDiagramArrowCurry_vertex
    {C : Type u} [Category.{u} C]
    (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry
        ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (Δ[1] : SSet.{u + 1})).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramPrismBase C ≫ H)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) Δ[1] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}).app
      (Opposite.op ⦋0⦌)
      (((pre ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
        (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramPrismBase C)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorVertex_precomposition, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex, Category.assoc]

/-- 同じ自然変換の積上の図式の curry は、元の prism から回収した同じ辺になる。 -/
lemma qCatDiagramArrowCurry_naturalTransformation_edge
    {C : Type u} [Category.{u} C] {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G) :
    ((((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry C).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow η))) 1)).app (Opposite.op ⦋1⦌)
          (𝟙 (Opposite.op ⦋1⦌))) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge η).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, qCatDiagramArrowCurry_vertex]
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex (L := (Δ[1] : SSet.{u + 1}))
      (curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
        (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramPrismBase C ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow η))))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}.edge =
      (ULift.up (𝟙 ⦋1⦌) : (Δ[1] : SSet.{u + 1}) _⦋1⦌) := by
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  rw [hi] at h ⊢
  exact h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
