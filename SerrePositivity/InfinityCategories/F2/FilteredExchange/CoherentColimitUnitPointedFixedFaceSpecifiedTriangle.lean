module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceOldComparison
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceLongTriangleComparison

/-!
概要：元の指定三角形比較の元の全空間射影による前合成を、始域比較と native 比較の合成へ同定。
方針：同じ長辺三証拠の合成則を、元の指定比較の既存の終点表示へ戻す。
規約：元の二単体・長辺証拠・指定同型の値を保持。使われ方：六面の比較の三関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "f" => fst (leftUnstraightening F)
  (coherentColimitUnitPointedTetrahedronChoice B T k)
local notation "V" => coherentTriangleOfFunctorTriangle S

/-- 元の指定三角形比較の前合成は、同じ長辺の指定始域比較と元の native 比較の合成。 -/
lemma coherentColimitUnitPointedFixedFaceSpecifiedTriangle_pre_heq_composite :
    HEq
      (VertexIso.map (unstraighteningTriangleRelativeVertexIso F Q₁ Q₂
        (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
        (V).diagram (V).first (V).second (V).long)
        (relativeFunctorPre (leftUnstraighteningProjection Q₂)
          (leftUnstraighteningProjection F) f))
      (coherentColimitUnitPointedFixedFaceLongSourceIso B T k j hj S hS ≪≫
        coherentColimitUnitPointedFixedFaceEndpointIso B T k j hj S hS) := by
  have hd := (coherentColimitUnitPointedFixedFaceLongCompositeIso_heq_old B T k j hj S hS).trans
    ((coherentColimitUnitPointedFixedFaceOldLongIso_heq_specified B T k j hj S hS).trans
      (functorTrianglePointedLift_comparison_pre S f).symm)
  exact hd.symm.trans
    (heq_of_eq (coherentColimitUnitPointedFixedFaceLongSource_native_trans B T k j hj S hS).symm)

end SerrePositivity.InfinityCategories.F2
