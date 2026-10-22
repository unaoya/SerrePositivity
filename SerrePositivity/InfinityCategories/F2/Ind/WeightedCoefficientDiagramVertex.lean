module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedLeftCoefficientEquivalence
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityCoefficient

/-!
概要：グラフ上の同じ係数分類図式の頂点は、元の全分類の指定添字での値そのもの。
方針：元の共同評価の curry を全次数で計算し、Indκ の同じ係数余錐の頂点へ接続する。
規約：頂点を同型な別の値へ置き換えない。使われ方：指定係数余錐の評価による余極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じグラフ上の係数分類は、元の全 weighted 分類の元の指定頂点そのもの。 -/
lemma weightedLeftCoefficientDiagram_vertex {B : SSet.{u}} [Quasicategory B]
    {I : Type u} [SmallCategory I] (F : I ⥤ LeftFibrationObject B) (i : I) :
    functorVertex (weightedLeftCoefficientDiagram F i) =
      (strictLeftWeightedClassification F).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i)) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の right 図式の同じ係数分類は、元の共同 right 分類の指定頂点そのもの。 -/
lemma weightedRightCoefficientDiagram_vertex {C : SSet.{u}} [Quasicategory C]
    {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C) (i : I) :
    functorVertex (weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i) =
      (strictRightWeightedClassification F).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i)) :=
  weightedLeftCoefficientDiagram_vertex (F ⋙ rightFibrationOppositeOrdinary C) i

/-- 元の同じ Indκ 係数余錐の指定頂点は、包含後に同じグラフ分類図式を厳密に回収する。 -/
lemma weightedIndDensityCoefficientCocone_vertex_inclusion (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
    (F : I ⥤ RightFibrationObject C)
    (hF : ∀ v, IsIndVertex κ C
      ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
        (Opposite.op ⦋0⦌) v)) (i : I) :
    (indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌)
      (weightedIndDensityCoefficientCocone κ F hF i).vertex =
        functorVertex
          (weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i) := by
  rw [weightedIndDensityCoefficientCocone_vertex]
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i)))
    (weightedIndClassification_inclusion κ F hF)
  exact h.trans (weightedRightCoefficientDiagram_vertex F i).symm

end SerrePositivity.InfinityCategories.F2.Ind
