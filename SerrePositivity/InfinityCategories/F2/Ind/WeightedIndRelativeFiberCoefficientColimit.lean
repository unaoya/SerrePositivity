module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeFiberTransformation

/-!
概要：元の相対 join の実際の fiber 余錐と左 Kan 像は、係数同型で戻したまま余極限。
方針：同じ標準変換の厳密な同定と、同じ係数単位から実現した余錐の全比較を使う。
規約：実際の fiber 余錐を選び直さない。使われ方：元の全図式の全 fiber 局所普遍性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I)

/-- 実際の相対 join fiber 余錐を同じ係数全空間へ戻した余錐は、元の係数図式の余極限。 -/
lemma weightedIndRelativeFiberCoefficientCocone_isColimit :
    IsColimitCone (weightedIndRelativeFiberCoefficientCocone κ F hF i) := by
  apply isColimitCone_of_coconeTransformationIso
    (weightedIndRelativeCoefficientCocone κ F hF i) _ (weightedIndCoefficientVertex κ F hF i)
    (weightedIndRelativeCoefficientCocone_vertex κ F hF i)
    (weightedIndRelativeFiberCoefficientCocone_vertex κ F hF i) _
    (weightedIndRelativeCoefficientCocone_isColimit κ F hF i)
  exact homotopyCoconeTransformationIso (weightedIndRelativeCoefficientHomotopy κ F hF i)
    (weightedIndRelativeCoefficientRealization κ F hF i) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (weightedIndRelativeFiberCoefficientTransformationVertex_eq κ F hF i).symm)

/-- 同じ実際の fiber 余錐を係数へ戻したまま、元の左 Kan 延長の像も余極限となる。 -/
lemma weightedIndRelativeFiberCoefficientCocone_image_isColimit
    [IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    IsColimitCone (mapJoinCocone G (weightedIndRelativeFiberCoefficientCocone κ F hF i)) := by
  let c := weightedIndRelativeCoefficientCocone κ F hF i
  let d := weightedIndRelativeFiberCoefficientCocone κ F hF i
  have hGc : IsColimitCone (mapJoinCocone G c) :=
    weightedIndRelativeCoefficientCocone_image_isColimit κ F hF i β hβ
  exact hGc.of_functorIso ((coconeFunctorIsoOfVertexIso c d (colimitConeIso c d
    (weightedIndRelativeCoefficientCocone_isColimit κ F hF i)
    (weightedIndRelativeFiberCoefficientCocone_isColimit κ F hF i))).postcomp G)

end SerrePositivity.InfinityCategories.F2.Ind
