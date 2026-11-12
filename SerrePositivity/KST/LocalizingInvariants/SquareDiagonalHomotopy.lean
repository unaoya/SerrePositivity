module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareDiagonalHomotopy

public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalShape
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：元の辺の比較を、下側三角形・共通対角・上側三角形の全 h Fun 合成に分解する。
方針：正方形の形状の合成三角形を元のホモトピーへ続けて curry する。
規約：比較辺を選び直さず、長辺は元の正方形。使われ方：native 右辺 prism の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareDiagonal

variable {X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⟶ X} (H : SSet.Homotopy F G)

def afterBottom : SSet.Homotopy F (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.diagonal H) where
  h := postShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ H.h
  h₀ := by
    rw [← Category.assoc, postShape_zero, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_bottom, H.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, postShape_one, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

def beforeTop : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.diagonal H) G where
  h := preShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ H.h
  h₀ := by
    rw [← Category.assoc, preShape_zero, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]
    rfl
  h₁ := by
    rw [← Category.assoc, preShape_one, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_top, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

def compositionTriangle : Truncated.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (afterBottom H))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (beforeTop H)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) where
  simplex := SSet.yonedaEquiv (curry (factor ≫ H.h))
  d₂ := by
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 2
      (SSet.yonedaEquiv (curry (factor ≫ H.h))) = SSet.yonedaEquiv (curry (afterBottom H).h)
    have he : stdSimplex.δ (2 : Fin 3) ≫ curry (factor ≫ H.h) = curry (afterBottom H).h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc, factor_first]
      rfl
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]
  d₀ := by
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 0
      (SSet.yonedaEquiv (curry (factor ≫ H.h))) = SSet.yonedaEquiv (curry (beforeTop H).h)
    have he : stdSimplex.δ (0 : Fin 3) ≫ curry (factor ≫ H.h) = curry (beforeTop H).h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc, factor_last]
      rfl
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]
  d₁ := by
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 1
      (SSet.yonedaEquiv (curry (factor ≫ H.h))) = SSet.yonedaEquiv (curry H.h)
    have he : stdSimplex.δ (1 : Fin 3) ≫ curry (factor ≫ H.h) = curry H.h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc,
        factor_long, Category.id_comp]
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]

lemma homMk_decomposition :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (afterBottom H)) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (beforeTop H)) :=
  (Truncated.HomotopyCategory.homMk_comp_homMk (compositionTriangle H)).symm

end SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
