module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonFaces

/-!
概要：比較の三点添字上の実際の合成三角形。
方針：有限順序の二つの合成可能射の nerve の二単体を使う。
規約：三辺は既存の二点添字の辺の各面への像。
使われ方：比較の族を転置して実際の三辺を持つ三角形を得る。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：三点添字には二点の標準辺の三つの像を面とする合成三角形がある。
方針：零から一、一から二への射列の nerve の二単体を計算する。
規約：三辺の射は選び直さない。
使われ方：全対象の比較の合成三角形の添字。 -/
def kanEnrichedComparisonIndexTriangle :
    SSet.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.map
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonFirstIndex)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.map
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonSecondIndex)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.map
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonLongIndex))) where
  simplex := ULift.up (ComposableArrows.mk₂
    (homOfLE (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 by decide))
    (homOfLE (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 by decide)))
  d₂ := by
    apply ULift.ext
    apply CategoryTheory.Functor.ext
    · intro i j f
      exact Subsingleton.elim _ _
    · intro i
      fin_cases i <;> rfl
  d₀ := by
    apply ULift.ext
    apply CategoryTheory.Functor.ext
    · intro i j f
      exact Subsingleton.elim _ _
    · intro i
      fin_cases i <;> rfl
  d₁ := by
    apply ULift.ext
    apply CategoryTheory.Functor.ext
    · intro i j f
      exact Subsingleton.elim _ _
    · intro i
      fin_cases i <;> rfl

/-- 概要：転置は添字の制限と厳密に可換。
方針：curry の単射性と二変数の交換の評価を計算する。
規約：単射や充填性を要求しない。
使われ方：実現した三角形の辺を既存の比較の辺へ戻す。 -/
lemma transposeFunctorFamily_pre {A I J X : SSet.{u}}
    (F : A ⟶ (ihom I).obj X) (i : J ⟶ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (F ≫ (pre i).app X) = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily, uncurry_curry, uncurry_pre_app, uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily, uncurry_curry]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
