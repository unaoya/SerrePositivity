module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCosliceFiber
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceFiberComparison
public import SerrePositivity.InfinityCategories.Derived.DGLeftPinchedFunctorMap
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  (F : DGFunctor R D E) (x : D) (q : E) (y : D)
  (s : ForgetEnrichment.of (Complex R) q ⟶ ForgetEnrichment.of (Complex R) (F.obj x))
/-- 同じ dg 関手像に同じ閉射を始点前合成した、実 coslice 全体の比較射。 -/
def dgFunctorClosedCosliceMap : dgVertexCoslice R D x ⟶ dgVertexCoslice R E q :=
  dgFunctorCoslicePostcomp R F x ≫ dgCoslicePrecompose R E (F.obj x) q s
/-- 同じ実合成比較は、元の同じ dg nerve 関手を底に持つ。 -/
lemma dgFunctorClosedCosliceMap_projection :
    dgFunctorClosedCosliceMap R F x q s ≫
      sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex q)) =
    sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex x)) ≫
      dgNerve.map F := by
  rw [dgFunctorClosedCosliceMap, Category.assoc, dgCoslicePrecompose_projection,
    dgFunctorCoslicePostcomp_projection]
/-- 同じ実合成比較が誘導する、標準終点上の実 fiber 射。 -/
def dgFunctorClosedCosliceFiber :
    vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex x))) (Simplex.vertex y) ⟶
    vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R E)).symm
      (Simplex.vertex q))) (Simplex.vertex (F.obj y)) :=
  transportSquareFiberMap _ _ (dgFunctorClosedCosliceMap R F x q s) (dgNerve.map F)
    (dgFunctorClosedCosliceMap_projection R F x q s) (Simplex.vertex y) ≫
      eqToHom (congrArg (vertexFiber (sliceUnderProjection
        ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex q))))
          (dgFunctorNerve_vertex F y))
/-- 同じ実合成 fiber 射は、元の実全空間への包含と可換。 -/
lemma dgFunctorClosedCosliceFiber_ι :
    dgFunctorClosedCosliceFiber R F x q y s ≫
      vertexFiberι (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R E)).symm
        (Simplex.vertex q))) (Simplex.vertex (F.obj y)) =
      vertexFiberι (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
        (Simplex.vertex x))) (Simplex.vertex y) ≫ dgFunctorClosedCosliceMap R F x q s := by
  rw [dgFunctorClosedCosliceFiber, Category.assoc,
    dgVertexFiberEqTransport_ι _ (dgFunctorNerve_vertex F y), transportSquareFiberMap_ι]
/-- 同じ実合成 fiber 射は、元の後合成・前合成の実 fiber 射の合成そのもの。 -/
lemma dgFunctorClosedCosliceFiber_factorization :
    dgFunctorClosedCosliceFiber R F x q y s =
      dgFunctorCosliceFiber R F x y ≫ dgCoslicePrecomposeFiber R E (F.obj x) q (F.obj y) s := by
  apply vertexFiber_hom_ext (sliceUnderProjection
    ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex q)))
    (Simplex.vertex (F.obj y))
  rw [dgFunctorClosedCosliceFiber_ι, Category.assoc, dgCoslicePrecomposeFiber,
    vertexFiberMap_ι, ← Category.assoc, dgFunctorCosliceFiber_ι, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories
