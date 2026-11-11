module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCosliceFiber
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedCosliceFiberComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLeftPinchedFunctorMap
/-!
概要：同じ dg 関手の実 coslice 後合成と閉始点前合成を、同じ実 fiber 射へ接続する。
方針：合成した全空間写像の fiber を標準終点へ正規化し、元の二つの実 fiber 射へ分解する。
規約：対象の小ささを仮定しない。使われ方：Hom 単位による全関手族の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (x : D) (q : E) (y : D)
  (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x))
/-- 同じ dg 関手像に同じ閉射を始点前合成した、実 coslice 全体の比較射。 -/
def dgFunctorClosedCosliceMap : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R D x ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R E q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp R F x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecompose R E (F.obj x) q s
/-- 同じ実合成比較は、元の同じ dg nerve 関手を底に持つ。 -/
lemma dgFunctorClosedCosliceMap_projection :
    dgFunctorClosedCosliceMap R F x q s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  rw [dgFunctorClosedCosliceMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecompose_projection,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp_projection]
/-- 同じ実合成比較が誘導する、標準終点上の実 fiber 射。 -/
def dgFunctorClosedCosliceFiber :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap _ _ (dgFunctorClosedCosliceMap R F x q s) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
    (dgFunctorClosedCosliceMap_projection R F x q s) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q))))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y))
/-- 同じ実合成 fiber 射は、元の実全空間への包含と可換。 -/
lemma dgFunctorClosedCosliceFiber_ι :
    dgFunctorClosedCosliceFiber R F x q y s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫ dgFunctorClosedCosliceMap R F x q s := by
  rw [dgFunctorClosedCosliceFiber, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexFiberEqTransport_ι _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap_ι]
/-- 同じ実合成 fiber 射は、元の後合成・前合成の実 fiber 射の合成そのもの。 -/
lemma dgFunctorClosedCosliceFiber_factorization :
    dgFunctorClosedCosliceFiber R F x q y s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCosliceFiber R F x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeFiber R E (F.obj x) q (F.obj y) s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))
  rw [dgFunctorClosedCosliceFiber_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeFiber,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCosliceFiber_ι, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
