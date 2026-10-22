module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerComposite
public import SerrePositivity.InfinityCategories.F2.UnstraighteningTriangleFamilyValueTransport
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleRelativeFamilyValue

/-!
概要：下面の指定区間族比較の成分を、元の全下面の相対比較へ値まで同定する。
方針：同じ単位・区間変換・対角を全族として照合し、元の一点成分へ戻す。
規約：元の下面や輸送を選び直さない。使われ方：下面作用比較の指定共役因子の分離。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 下面の元の区間族比較は、同じ全下面から得た元の相対比較の指定値を保持する。 -/
lemma coherentColimitLowerCompositeIso_app_heq_triangle :
    HEq ((coherentColimitLowerCompositeIso B H).app
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
      (functorTriangleRelativeComparison (coherentColimitTargetLowerTriangle B H)) := by
  refine HEq.trans ?_
    (functorTriangleRelativeComparison_heq_family_app
      (coherentColimitTargetLowerTriangle B H)).symm
  unfold coherentColimitLowerCompositeIso
  dsimp only
  apply unstraighteningMappingTriangleIso_app_heq_of_family_eq
  · exact congrArg SSet.const
      (coherentVertexOfHomotopy_cocone (coherentDiagramTotalCocone F)).symm
  · simpa only [SSet.yonedaEquiv_symm_zero] using coherentColimitIntervalVertex_constant B H
  · rfl

end SerrePositivity.InfinityCategories.F2
