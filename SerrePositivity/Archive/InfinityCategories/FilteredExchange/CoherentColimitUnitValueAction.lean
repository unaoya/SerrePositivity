module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareConstantTargetTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitNativeUnitValueComparison

/-!
概要：元の単位正方形の二面比較を、元の定値余錐頂点の値へ写す。
方針：元の相対 Hom 同型と fiber の値の比較を使い、native 標的表示との値の一致を保つ。
規約：元の全係数・二面・指定値を保持。使われ方：三角形整合式全体を値へ写す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) {C : SSet.{u + 1}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
  (p : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)
  (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌)

/-- 元の二面の指定比較を、元の標的余錐の値へ写した同じ全係数の比較。 -/
def coherentColimitUnitValueAction :=
  VertexIso.map (coherentColimitUnitValueComparison B H p x)
    ((constantUnstraighteningRelativeIso p (coherentDiagramTotalCocone G).vertex).hom ≫
      (ihom C).map (pointedSpaceFiberValueEquivalence (coherentDiagramTotalCocone G).vertex).hom)

/-- 元の値への像は、native 標的へ同じ二面を表示変更してから写した像と一致する。 -/
lemma coherentColimitUnitValueAction_heq_native :
    HEq (coherentColimitUnitValueAction B H p x)
      (VertexIso.map (coherentColimitNativeUnitValueComparison B H p x)
        ((constantUnstraighteningRelativeIso p (coherentDiagramTotalVertex G)).hom ≫
          (ihom C).map (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)) :=
  functorSquareComparison_value_heq_target
    (coherentColimitUnitUpperTriangle B H) (coherentColimitUnitLowerTriangle B H)
    (coherentColimitNativeUnitFunctorTriangle B H) (coherentColimitTargetLowerTriangle B H)
    (coherentDiagramTotalCocone_vertex G) (coherentNativeUnitHomotopy_h G).symm
    rfl rfl rfl rfl p x

end SerrePositivity.InfinityCategories.F2
