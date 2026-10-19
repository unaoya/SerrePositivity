module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentHomNaturality

/-!
概要：任意の coherent な余錐の頂点からの全 Hom による余錐の族と、部分余極限への制限を計算する。
方針：coslice の left fibration に任意の点の Hom の族を適用し、実際の付加比較辺の前合成へ移す。
規約：元の余錐の余極限性は仮定しない。使われ方：貼った余錐の普遍点の非循環な検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {F : K ⟶ X}

/-- 任意の余錐の頂点からの全左 Hom による、固定終点余錐空間の実際の族。 -/
def coconePointHomFamily (d : JoinCocone F) (y : X _⦋0⦌) :
    pinchedHomLeft d.vertex y ⟶ coconeMappingSpace F y :=
  leftFibrationPointHomFamily (sliceUnderProjection F) d y

/-- 元の余錐が余極限なら、その全 Hom による余錐の族は実際のホモトピー同値。 -/
lemma coconePointHomFamily_homotopyEquivalence (d : JoinCocone F) (hd : IsColimitCone d)
    (y : X _⦋0⦌) : IsSimplicialHomotopyEquivalence (coconePointHomFamily d y) :=
  leftFibrationPointHomFamily_homotopyEquivalence (sliceUnderProjection F) d y hd

/-- 任意の余錐の全 Hom の族の制限は、実際の付加比較辺による前合成と全単体でホモトピック。 -/
lemma coconePointHomFamily_restriction_homotopy {A : SSet.{u}} {p : A ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ K) (hi : i ≫ F = p)
    (d : JoinCocone F) (y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy
      ((coconePointHomFamily d y ≫ normalizedCoconeRestrictionFiber F i hi y) ≫
        coconeMappingSpaceHomComparison c hc y)
      (colimitAttachmentHomPrecomposition c hc i F hi d y)) :=
  pointHomFamily_restriction_comparison_homotopy (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

end
end SerrePositivity.InfinityCategories.HomotopyLimits
