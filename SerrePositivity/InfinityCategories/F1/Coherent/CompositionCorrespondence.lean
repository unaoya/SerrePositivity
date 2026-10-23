module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionFixedTriangle
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CompositionCorrespondenceCurry
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CompositionCorrespondenceDiagonal

/-!
概要：元の豊穣 Hom から、同じ第二射を固定した合成三角形全体への比較を構成する。
方針：coherent 合成三角形を元の pullback へ curry し、第一辺の標準比較で同値性を示す。
規約：同じ三角形と第一辺の全パラメーターを保持する。
使われ方：後合成・対角評価の二つの Kan fibration の全空間を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C) (f : Y ⟶ Z)

/-- 元の第一 Hom を、同じ第二射の coherent な合成三角形全体へ写す。 -/
def coherentCompositionCorrespondence :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶
      compositionCorrespondence (coherentNerveVertex X) (coherentNerveEdge f) :=
  compositionCorrespondenceCurry _ _ (coherentHomIntervalComparison X Y)
    (coherentCompositionFixedTriangle X Y Z f)
    (coherentCompositionFixedTriangle_first X Y Z f)
    (coherentCompositionFixedTriangle_last X Y Z f)

/-- 同じ全空間比較の第一辺射影は、元の標準 Hom 比較そのもの。 -/
lemma coherentCompositionCorrespondence_first :
    coherentCompositionCorrespondence X Y Z f ≫
        compositionCorrespondenceFirst (coherentNerveVertex X) (coherentNerveEdge f) =
      coherentHomIntervalComparison X Y :=
  compositionCorrespondenceCurry_first _ _ _ _ _ _

/-- 同じ全空間比較の三角形は、元の coherent 合成三角形を厳密に回収する。 -/
lemma coherentCompositionCorrespondence_triangle :
    coherentCompositionCorrespondence X Y Z f ≫
        pullback.fst ((pre (horn 2 1).ι).app (SimplicialNerve C))
          (composableHomHornMap (coherentNerveVertex X) (coherentNerveEdge f)) =
      curry (coherentCompositionFixedTriangle X Y Z f) :=
  compositionCorrespondenceCurry_triangle _ _ _ _ _ _

/-- 同じ全空間比較の評価も、元の全パラメーターの coherent 合成三角形。 -/
lemma coherentCompositionCorrespondence_evaluation :
    (Δ[2] ◁ coherentCompositionCorrespondence X Y Z f) ≫
        compositionCorrespondenceEvaluation (coherentNerveVertex X) (coherentNerveEdge f) =
      coherentCompositionFixedTriangle X Y Z f :=
  compositionCorrespondenceCurry_evaluation _ _ _ _ _ _

/-- 同じ全空間比較の対角評価は、元の coherent 合成三角形の同じ対角。 -/
lemma coherentCompositionCorrespondence_diagonal_uncurry :
    intervalMappingUncurry (coherentCompositionCorrespondence X Y Z f ≫
      compositionCorrespondenceDiagonal (coherentNerveVertex X) (coherentNerveEdge f)) =
      (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ coherentCompositionFixedTriangle X Y Z f := by
  rw [intervalMappingUncurry_precomp, compositionCorrespondenceDiagonal_uncurry,
    ← Category.assoc, whisker_exchange, Category.assoc,
    coherentCompositionCorrespondence_evaluation]

attribute [local instance] compositionCorrespondence_kanComplex

/-- 局所 Kan な場合、元の豊穣 Hom から同じ合成三角形全体への実際の比較は同値。 -/
lemma coherentCompositionCorrespondence_isQCatEquivalence
    [∀ A B : C, KanComplex (SimplicialCategory.sHom A B)] :
    IsQCatEquivalence (coherentCompositionCorrespondence X Y Z f) := by
  apply (compositionCorrespondenceFirst_isQCatEquivalence
    (coherentNerveVertex X) (coherentNerveEdge f)).cancel_right
  rw [coherentCompositionCorrespondence_first]
  exact coherentHomIntervalComparison_isQCatEquivalence X Y

end SerrePositivity.InfinityCategories
