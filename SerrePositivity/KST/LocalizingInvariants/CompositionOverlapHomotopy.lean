module

public import SerrePositivity.KST.LocalizingInvariants.CompositionOverlapShape
public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalHomotopy

/-!
概要：四頂点単体の隣接二面から作る辺比較の合成を、残る二面の合成と同定する。
方針：同じ全三角形族を curry し、その長辺を正方形の対角分解で計算する。
規約：端点だけでなく各ホモトピーの全射を保持。使われ方：模型右辺の合成貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CompositionOverlap

variable {X : SSet.{u}} {U V W : (Δ[1] : SSet.{u}) ⟶ X}
  (S : (Δ[3] : SSet.{u}) ⟶ X) (P : SSet.Homotopy U V) (Q : SSet.Homotopy V W)
  (hP : P.h = SquareDiagonal.preShape ≫ stdSimplex.δ (3 : Fin 4) ≫ S)
  (hQ : Q.h = SquareDiagonal.postShape ≫ stdSimplex.δ (0 : Fin 4) ≫ S)

include hP hQ in
def longHomotopy : SSet.Homotopy U W where
  h := square ≫ S
  h₀ := by
    rw [← Category.assoc, square_source, Category.assoc]
    have he := P.h₀
    rw [hP, ← Category.assoc, SquareDiagonal.preShape_zero] at he
    exact he
  h₁ := by
    rw [← Category.assoc, square_target, Category.assoc]
    have he := Q.h₁
    rw [hQ, ← Category.assoc, SquareDiagonal.postShape_one] at he
    exact he
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

def compositionTriangle : Truncated.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy P) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (longHomotopy S P Q hP hQ)) where
  simplex := SSet.yonedaEquiv (curry (overlap ≫ S))
  d₂ := by
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 2
      (SSet.yonedaEquiv (curry (overlap ≫ S))) = SSet.yonedaEquiv (curry P.h)
    have he : stdSimplex.δ (2 : Fin 3) ≫ curry (overlap ≫ S) = curry P.h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc,
        overlap_first, Category.assoc]
      exact hP.symm
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]
  d₀ := by
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 0
      (SSet.yonedaEquiv (curry (overlap ≫ S))) = SSet.yonedaEquiv (curry Q.h)
    have he : stdSimplex.δ (0 : Fin 3) ≫ curry (overlap ≫ S) = curry Q.h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc,
        overlap_last, Category.assoc]
      exact hQ.symm
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]
  d₁ := by
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 1
      (SSet.yonedaEquiv (curry (overlap ≫ S))) =
        SSet.yonedaEquiv (curry (longHomotopy S P Q hP hQ).h)
    have he : stdSimplex.δ (1 : Fin 3) ≫ curry (overlap ≫ S) =
        curry (longHomotopy S P Q hP hQ).h := by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc,
        overlap_long]
      rfl
    rw [← stdSimplex.yonedaEquiv_δ_comp, he]

lemma homMk_overlap :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy P) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q) =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (SquareDiagonal.afterBottom (longHomotopy S P Q hP hQ))) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (SquareDiagonal.beforeTop (longHomotopy S P Q hP hQ))) := by
  rw [Truncated.HomotopyCategory.homMk_comp_homMk (compositionTriangle S P Q hP hQ)]
  exact SquareDiagonal.homMk_decomposition _

lemma afterBottom_map : (SquareDiagonal.afterBottom (longHomotopy S P Q hP hQ)).h =
    SquareDiagonal.postShape ≫ stdSimplex.δ (1 : Fin 4) ≫ S := by
  change _ ≫ _ ≫ (square ≫ S) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1), square_lower]

lemma beforeTop_map : (SquareDiagonal.beforeTop (longHomotopy S P Q hP hQ)).h =
    SquareDiagonal.preShape ≫ stdSimplex.δ (2 : Fin 4) ≫ S := by
  change _ ≫ _ ≫ (square ≫ S) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0), square_upper]

end SerrePositivity.KST.LocalizingInvariants.CompositionOverlap
