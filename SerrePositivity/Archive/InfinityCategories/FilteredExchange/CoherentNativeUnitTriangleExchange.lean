module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration

/-!
概要：元の native 単位の指定値の比較を、同じ全三角形比較と交換する。
方針：元の単位表現の指定同型に関手同型の前後合成の交換則を適用する。
規約：元の二つの指定同型を保持。使われ方：三角形に沿う上側の単位因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)

/-- 同じ全三角形の後合成と元の単位表現の比較は、同じ三つの作用の前合成で整合する。 -/
lemma coherentNativeUnitValueIso_triangle_exchange :
    (functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J) ≪≫
      (coherentNativeUnitValueIso J).precomp
        ((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val) =
      (coherentNativeUnitValueIso J).precomp
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).val ≪≫
          (functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J) :=
  functorIso_whisker_exchange (functorTriangleTotalActionIso T) (coherentNativeUnitValueIso J)

end SerrePositivity.InfinityCategories.F2
