module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberBoundaryCandidateComponents

/-! # 標準 fiber の左右の充填単体の共通面

概要：左右の明示解を挿入した単体は先頭と D からなる共通面で一致する。
方針：挿入成分は共通の型付き解と比較し、それ以外は零未知基底の一致へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二つの標準セルの貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：左右の候補データは共通面へ制限すると等しい。
方針：対象を元の共通面から同定し、二つの挿入集合と残りの集合を分けて成分を比較する。
規約：HA Proposition 1.3.1.10。使われ方：左右の単体を貼るための整合条件。 -/
lemma dgModuleFiberBoundaryCandidate_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) := by
  have hi : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n).succAboveOrderEmb.injective
  have hbase : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryZeroData_common (A := A) (D := RightModule A D) (n := n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)
  have hobj : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom
    n)).obj =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n)).obj := by
    funext i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryZeroData_common_obj (A := A) (D := RightModule A D) (n := n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b) i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro J a c k hJ ha hc hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
  by_cases h0 : J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate_prefix_heq A D f b hb _ h0 _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate_prefix_heq A D f b hb _ h0 _ _ _ _ _ _ _).symm
  · by_cases hD : J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) =
        insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)
    · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate_last_heq A D f b hb _ hD _ _ _ _ _ _ _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate_last_heq A D f b hb _ hD _ _ _ _ _ _ _).symm
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate_hom_of_ne A D f b hb _ h0 hD,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate_hom_of_ne A D f b hb _ h0 hD]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) hbase J a c k hJ ha hc hk hi.injOn hi.injOn

/-- 概要：左右の実際の dg nerve の単体は共通面へ制限すると等しい。
方針：候補データの共通面の等式を単体の外延性で持ち上げる。
規約：HA Proposition 1.3.1.10。使われ方：join の二セルの押し出しによる貼合せ。 -/
lemma dgModuleFiberBoundarySimplex_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftSimplex A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightSimplex A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (dgModuleFiberBoundaryCandidate_common A D f b hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
