module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientEvaluation
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorIsPullbackIso

/-!
概要：元の weighted 係数包含は、同じ添字のグラフ上の厳密な引き戻し。
方針：元の係数射影と底の定値包含を検査し、既存の同じグラフ同型の両射影を使う。
規約：全空間の同値だけで代用しない。使われ方：各段の元の相対評価空間への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {A : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : A ⟶ (CategoryTheory.Functor.const I).obj B) (i : I)

/-- 元の係数包含は、同じ係数射影と添字グラフを厳密に結ぶ。 -/
lemma weightedCoefficient_graph_commute :
    weightedNerveConstantLift A i ≫ weightedNerveParameterProjection η =
      η.app i ≫ underSectionFiberBase B i := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, weightedNerveParameterProjection, underSectionFiberBase,
      lift_fst, Category.comp_id]
    exact weightedNerveConstantLift_parameter η i
  · simp only [Category.assoc, weightedNerveParameterProjection, underSectionFiberBase,
      lift_snd, SSet.comp_const]
    exact weightedNerveConstantLift_projection A i

/-- 元の係数値への制限は、元の共同射影と同じ添字グラフの引き戻しそのもの。 -/
lemma weightedCoefficient_isPullback :
    IsPullback (weightedNerveConstantLift A i) (η.app i)
      (weightedNerveParameterProjection η) (underSectionFiberBase B i) :=
  IsPullback.of_iso_pullback ⟨weightedCoefficient_graph_commute η i⟩
    (weightedParameterGraphIso η i) (weightedParameterGraphIso_fst η i)
    (weightedParameterGraphIso_snd η i)

end SerrePositivity.InfinityCategories.F2.Ind
