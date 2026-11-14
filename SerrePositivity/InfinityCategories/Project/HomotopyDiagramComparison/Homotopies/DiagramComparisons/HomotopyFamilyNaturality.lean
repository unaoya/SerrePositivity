module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyConstantFamily

/-!
概要：指定ホモトピーの自然性を、任意の区間写像空間の族で表す。
方針：族と指定円柱から関手単体集合内の正方形を作り、四辺と合成を照合する。
規約：元の標準の前後合成を保持。使われ方：Quillen 導来単位の標準比較の可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A X Y : SSet.{u}} {U V : X ⟶ Y}
  (H : SSet.Homotopy U V) {x y : X _⦋0⦌}
  (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
/-- 元のホモトピーと任意の区間族から、関手単体集合内の正方形を作る。 -/
def homotopyFamilySquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj Y :=
  curry ((α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) ≫ H.h)
/-- 正方形の下辺は、元の始点関手による区間族の像である。 -/
lemma homotopyFamilySquare_bottom : SSet.ι₀ ≫ homotopyFamilySquare H f =
    curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U x y)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, homotopyFamilySquare, uncurry_curry, uncurry_curry]
  have he : (A ◁ SSet.ι₀) ≫ (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ≫ SSet.ι₀ := by rfl
  change ((A ◁ SSet.ι₀) ≫
    (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
  rw [he, Category.assoc, H.h₀]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f ≫ U = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap_uncurry]
  rfl
/-- 正方形の上辺は、元の終点関手による区間族の像である。 -/
lemma homotopyFamilySquare_top : SSet.ι₁ ≫ homotopyFamilySquare H f =
    curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap V x y)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, homotopyFamilySquare, uncurry_curry, uncurry_curry]
  have he : (A ◁ SSet.ι₁) ≫ (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ≫ SSet.ι₁ := by rfl
  change ((A ◁ SSet.ι₁) ≫
    (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
  rw [he, Category.assoc, H.h₁]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f ≫ V = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap_uncurry]
  rfl
/-- 二つの側辺は、元の両端点での指定ホモトピーの制限である。 -/
lemma homotopyFamilySquare_side (i : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ homotopyFamilySquare H f =
    curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H
      (SSet.const (if i = 0 then x else y) : A ⟶ X)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, homotopyFamilySquare, uncurry_curry, uncurry_curry]
  fin_cases i
  · have he : (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})) ≫
        (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
          ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h) ▷ Δ[1] := by rfl
    change ((A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})) ≫
      (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
    rw [he, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h₀]
    rfl
  · have he : (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u})) ≫
        (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u})) =
          ((SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h) ▷ Δ[1] := by rfl
    change ((A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u})) ≫
      (α_ A (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h ▷ (Δ[1] : SSet.{u}))) ≫ H.h = _
    rw [he, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h₁]
    rfl
/-- 任意の区間族上で、指定ホモトピーの自然性の合成式が成り立つ。 -/
lemma homotopyFamily_composition [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U x y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap V x y) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hq := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U x y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap V x y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyConstantFamily (A := A) H x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyConstantFamily (A := A) H y))
    (homotopyFamilySquare H f) ?_ ?_ ?_ ?_
  · rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyConstantFamily_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyConstantFamily_hom] at hq
    exact hq
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_bottom H f)
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_top H f)
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_side H f 0)
  · change (homotopyFamilySquare H f).app (Opposite.op ⦋1⦌)
      (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ homotopyFamilySquare H f) = _
    exact congrArg SSet.yonedaEquiv (homotopyFamilySquare_side H f 1)

/-- 指定ホモトピーの自然性は、標準の前後合成を結ぶ単体的ホモトピーを与える。 -/
lemma intervalFunctorMap_homotopy_naturality [Quasicategory Y] :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (U.app (Opposite.op ⦋0⦌) x)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap V x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (V.app (Opposite.op ⦋0⦌) y)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose_family, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family]
  simpa only [Category.id_comp] using homotopyFamily_composition H
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
