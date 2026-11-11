module

public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalHomotopy

/-!
概要：指定された全三角形族から、三つの辺ホモトピーの合成式を作る。
方針：全族を curry し、三面の全射の等号を元の辺の合成構造へ移す。
規約：合成の結論を入力しない。使われ方：標準三角形の同側比較の結合律。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyTriangle

variable {A X : SSet.{u}} {F G H : A ⟶ X}
  (P : SSet.Homotopy F G) (Q : SSet.Homotopy G H) (R : SSet.Homotopy F H)
  (T : A ⊗ Δ[2] ⟶ X)
  (h₂ : (A ◁ stdSimplex.δ (2 : Fin 3)) ≫ T = P.h)
  (h₀ : (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ T = Q.h)
  (h₁ : (A ◁ stdSimplex.δ (1 : Fin 3)) ≫ T = R.h)

def composition : Truncated.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy R) where
  simplex := SSet.yonedaEquiv (curry T)
  d₂ := by
    change ((ihom A).obj X).δ 2 (SSet.yonedaEquiv (curry T)) =
      SSet.yonedaEquiv (curry P.h)
    have he : stdSimplex.δ (2 : Fin 3) ≫ curry T = curry P.h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, h₂]
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]
  d₀ := by
    change ((ihom A).obj X).δ 0 (SSet.yonedaEquiv (curry T)) =
      SSet.yonedaEquiv (curry Q.h)
    have he : stdSimplex.δ (0 : Fin 3) ≫ curry T = curry Q.h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, h₀]
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]
  d₁ := by
    change ((ihom A).obj X).δ 1 (SSet.yonedaEquiv (curry T)) =
      SSet.yonedaEquiv (curry R.h)
    have he : stdSimplex.δ (1 : Fin 3) ≫ curry T = curry R.h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, h₁]
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]

include T h₂ h₀ h₁ in
lemma homMk_comp : Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy P) ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy R) :=
  Truncated.HomotopyCategory.homMk_comp_homMk (composition P Q R T h₂ h₀ h₁)

end SerrePositivity.KST.LocalizingInvariants.HomotopyTriangle
