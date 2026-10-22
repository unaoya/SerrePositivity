module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientCoconeTransformation
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluationRestriction

/-!
概要：指定 native 係数余錐を、元の Indκ 包含と指定始点で評価する。
方針：写した図式・頂点・全余錐を保持し、共同図式の同じ制限との厳密な一致を記録する。
規約：評価余錐を選び直さない。使われ方：実際の評価変換の c1 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)

/-- 元の Indκ 包含を経た、同じ指定始点での評価。 -/
def indPresheafEvaluation := indInclusionPresheaf κ C ≫ presheafInfinityEvaluation x
local notation "q" => indPresheafEvaluation κ x

/-- 指定 native 係数余錐の元の図式を、同じ評価で写した図式。 -/
def weightedCoefficientNativeEvaluationDiagram := weightedIndCoefficientDiagram κ F i ≫ q

/-- 同じ native 係数余錐の指定頂点の元の評価。 -/
def weightedCoefficientNativeEvaluationVertex :=
  (indPresheafEvaluation κ x).app (Opposite.op ⦋0⦌) (weightedIndCoefficientVertex κ F hF i)

/-- 指定 native 係数余錐そのものの、元の評価による像。 -/
def weightedCoefficientNativeEvaluationCocone :
    JoinCocone (weightedCoefficientNativeEvaluationDiagram κ F i x) :=
  mapJoinCocone q (weightedIndDensityCoefficientCocone κ F hF i)

lemma weightedCoefficientNativeEvaluationCocone_vertex :
    (weightedCoefficientNativeEvaluationCocone κ F hF i x).vertex =
      weightedCoefficientNativeEvaluationVertex κ F hF i x := by
  rw [weightedCoefficientNativeEvaluationCocone, mapJoinCocone_vertex,
    weightedIndDensityCoefficientCocone_vertex]
  rfl

/-- 元の評価図式は、共同 Hom の係数・始点制限と同じ図式。 -/
lemma weightedCoefficientNativeEvaluationDiagram_eq :
    weightedCoefficientNativeEvaluationDiagram κ F i x =
      weightedCoefficientEvaluationDiagram F i x := by
  change _ ≫ (indInclusionPresheaf κ C ≫ presheafInfinityEvaluation x) = _
  rw [weightedIndCoefficientDiagram, Category.assoc, ← Category.assoc (indYoneda κ C),
    indYoneda_inclusion]
  rfl

/-- 元の評価頂点は、同じ共同係数分類の指定値そのもの。 -/
lemma weightedCoefficientNativeEvaluationVertex_eq :
    weightedCoefficientNativeEvaluationVertex κ F hF i x =
      weightedCoefficientEvaluationVertex F i x := by
  have h := weightedIndDensityCoefficientCocone_vertex_inclusion κ F hF i
  rw [weightedIndDensityCoefficientCocone_vertex] at h
  change (presheafInfinityEvaluation x).app (Opposite.op ⦋0⦌)
    ((indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌)
      (weightedIndCoefficientVertex κ F hF i)) = _
  rw [h]
  exact evaluateFunctorAt_functorVertex _ _

/-- 元の係数円柱を同じ評価で写し、元の評価図式と元の評価頂点を端点に保つ。 -/
def weightedCoefficientNativeEvaluationHomotopy :
    SSet.Homotopy (weightedCoefficientNativeEvaluationDiagram κ F i x)
      (SSet.const (weightedCoefficientNativeEvaluationVertex κ F hF i x)) where
  h := (weightedIndDensityCoefficientHomotopy κ F hF i).h ≫ q
  h₀ := by
    rw [← Category.assoc, (weightedIndDensityCoefficientHomotopy κ F hF i).h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, (weightedIndDensityCoefficientHomotopy κ F hF i).h₁, SSet.const_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.F2.Ind
