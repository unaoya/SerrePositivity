module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramArrowEndpoints

/-!
概要：二点と底の積上の Cat∞ 値図式を、底上の関手の区間族へ移す。
方針：元の区間と底の積の射列を前合成し、同じ関手空間の curry を使う。
規約：区間の両端で元の端点制限を厳密に回収する。
使われ方：底全体の分類主写像の間の実際の比較の辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ二点と底の積上の図式を、底上の関手 ∞ 圏の区間族へ写す。 -/
def qCatDiagramArrowCurry (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C))) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :=
  (pre ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (Δ[1] : SSet.{u + 1})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramPrismBase C)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) Δ[1] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}

/-- 同じ区間族の各端点は、元の二点と底の積上の図式の同じ端点制限。 -/
lemma qCatDiagramArrowCurry_endpoint (C : Type u) [Category.{u} C] (i : Fin 2) :
    qCatDiagramArrowCurry C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramEndpointIndex i C)))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 区間族の辺を底対象で評価すると、積上の同じ交差辺を回収する。 -/
lemma qCatDiagramArrowCurry_component (C : Type u) [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (Fin 2 × C))) _⦋1⦌) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).app _
      ((((qCatDiagramArrowCurry C).app _ F).app (Opposite.op ⦋1⦌)
        (𝟙 (Opposite.op ⦋1⦌))) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      F.app (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌))
        (ULift.up (nerve.edgeMk
          ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 c) :
            ((0 : Fin 2), c) ⟶ (1, c))).edge) := by
  apply congrArg (fun σ : (nerve (Fin 2 × C)) _⦋1⦌ ↦
    F.app (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌)) (ULift.up σ))
  change (SimplexCategory.toCat.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}.edge.down).toFunctor.prod'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) 1) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · apply Prod.ext
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}.edge.down.toOrderHom 0 : Fin 2) = 0
      decide
    · rfl
  · apply Prod.ext
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 1}.edge.down.toOrderHom 1 : Fin 2) = 1
      decide
    · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Prod.ext
    · change (homOfLE (show (0 : Fin 2) ≤ 1 by decide) : (0 : Fin 2) ⟶ 1) = _
      exact Subsingleton.elim _ _
    · change ((ComposableArrows.mk₀ c).map (𝟙 (0 : Fin 1))) = 𝟙 c
      exact CategoryTheory.Functor.map_id _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
