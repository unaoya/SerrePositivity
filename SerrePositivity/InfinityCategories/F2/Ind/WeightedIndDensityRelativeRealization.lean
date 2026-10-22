module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityCoefficient
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinTransformationClass

/-!
概要：元の weighted 密度変換を、両端と指定単位の類を保持する一つの相対 join 図式へ実現。
方針：既存の相対 join 円柱実現と、同じ円柱比較による両端の同時厳密化を使う。
規約：元の全変換と共同分類を固定。使われ方：同じ係数余錐の余極限性から大域比較へ戻す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v))

/-- 元の weighted 添字射影の同じ宇宙への持ち上げ。 -/
abbrev weightedIndDensityIndexProjection :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (rightFibrationTotalDiagram F))

/-- 元の weighted 全空間上の同じ Indκ 値の表現可能図式。 -/
abbrev weightedIndDensitySource :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedDensityProjection F) ≫ indYoneda κ C
local notation "p" => weightedIndDensityIndexProjection F
local notation "A" => weightedIndDensitySource κ F
local notation "B" => weightedIndClassification κ F hF

/-- 元の全変換の一つの相対 join 実現を、元の全円柱との比較とともに固定する。 -/
def weightedIndDensityRelativeRealization :
    LeftKanRelativeJoinRealization p A B (weightedIndDensityHomotopy κ F hF) :=
  Classical.choice (leftKanRelativeJoinRealization_nonempty p A B
    (weightedIndDensityHomotopy κ F hF))

/-- 同じ実現の両端を、一つの補正で元の二図式へ厳密化する。 -/
def weightedIndDensityRelativeStrictification :
    (weightedIndDensityRelativeRealization κ F hF).Strictification :=
  Classical.choice (weightedIndDensityRelativeRealization κ F hF).strictification_nonempty

/-- 同じ全変換を実現し、元の両端を厳密に持つ相対 join 図式。 -/
def weightedIndDensityRelativeDiagram : relativeJoin p (𝟙 _) ⟶ IndInfinity κ C :=
  (weightedIndDensityRelativeStrictification κ F hF).diagram

lemma weightedIndDensityRelativeDiagram_left : relativeJoinInl p (𝟙 _) ≫
    weightedIndDensityRelativeDiagram κ F hF = A :=
  (weightedIndDensityRelativeStrictification κ F hF).left_eq

lemma weightedIndDensityRelativeDiagram_right : relativeJoinInr p (𝟙 _) ≫
    weightedIndDensityRelativeDiagram κ F hF = B :=
  (weightedIndDensityRelativeStrictification κ F hF).right_eq

/-- 同じ相対 join 図式の prism を、元の全変換と同じ両端のホモトピーとして読む。 -/
def weightedIndDensityRelativeHomotopy : SSet.Homotopy A (p ≫ B) :=
  (weightedIndDensityRelativeStrictification κ F hF).transformation

/-- 同じ両端の厳密化は、元の指定単位の h Fun の類を保持する。 -/
lemma weightedIndDensityRelativeHomotopy_hom_eq :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (weightedIndDensityRelativeHomotopy κ F hF)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (weightedIndDensityHomotopy κ F hF)) :=
  (weightedIndDensityRelativeStrictification κ F hF).transformation_hom_eq

end SerrePositivity.InfinityCategories.F2.Ind
