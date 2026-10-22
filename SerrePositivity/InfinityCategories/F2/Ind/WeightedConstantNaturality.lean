module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityHomotopy
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedParameterGraphIso

/-!
概要：weighted の同じ係数包含は、元の自然変換と厳密に可換。
方針：同じ定値の底の射列と、全初区間の元の係数を比較する。
規約：係数の充填性は不要。使われ方：同じ全 twisted-arrow 評価の各 fiber への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の係数包含と元の自然変換は、weighted 全空間で厳密に可換。 -/
lemma weightedConstantLift_naturality {I : Type u} [Category.{u} I]
    {A B : I ⥤ SSet.{u}} (η : A ⟶ B) (i : I) :
    weightedNerveConstantLift A i ≫ weightedNerveMap η =
      η.app i ≫ weightedNerveConstantLift B i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  change (SSet.stdSimplex.map (simplexPrefixInclusion j.val n _) ≫
      SSet.yonedaEquiv.symm x) ≫ η.app i =
    SSet.stdSimplex.map (simplexPrefixInclusion j.val n _) ≫
      SSet.yonedaEquiv.symm ((η.app i).app _ x)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

/-- 同じ全密度図式の元の係数での底射影は、元の right fibration の射影そのもの。 -/
lemma weightedDensityProjection_coefficient {C : SSet.{u}} [Quasicategory C]
    {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C) (i : I) :
    weightedNerveConstantLift (rightFibrationTotalDiagram F) i ≫ weightedDensityProjection F =
      (F.obj i).val.hom :=
  weightedNerveConstantLift_parameter (rightFibrationProjectionCocone F).ι i

end SerrePositivity.InfinityCategories.F2.Ind
