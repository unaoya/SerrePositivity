module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCoslicePrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGLeftPinchedCoordinates
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
/-!
概要：同じ閉始点前合成を、指定終点上の実 fiber 射と左 pinched Hom の射へ移す。
方針：同じ射影等式から fiber 射を取り、左 Hom の全単体座標で像を計算する。
規約：全次数の実等式。使われ方：Hom の比較鎖同型を実 fiber 射へ反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (x q y : D) (s : ForgetEnrichment.of (Complex R) q ⟶ ForgetEnrichment.of (Complex R) x)
/-- 同じ閉始点前合成が誘導する、指定終点上の実 fiber 射。 -/
def dgCoslicePrecomposeFiber :
    vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex x))) (Simplex.vertex y) ⟶
    vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex q))) (Simplex.vertex y) :=
  vertexFiberMap _ _ (dgCoslicePrecompose R D x q s)
    (dgCoslicePrecompose_projection R D x q s) (Simplex.vertex y)
/-- 同じ実 fiber 射の全単体座標は、元の同じ閉始点細分。 -/
lemma dgCoslicePrecomposeFiber_simplex {n : ℕ}
    (u : (vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex x))) (Simplex.vertex y)) _⦋n⦌) :
    cosliceFiberSimplex n ((dgCoslicePrecomposeFiber R D x q y s).app _ u) =
      dgCoslicePrecomposeCoordinate R D x q s u.val := by
  change SSet.yonedaEquiv (dgPointCosliceSimplex _
    (dgCoslicePrecomposeSimplex R D x q s u.val)) = _
  unfold dgCoslicePrecomposeSimplex
  rw [dgPointCosliceSimplexOfFixed_simplex, Equiv.apply_symm_apply]
/-- 同じ実 fiber 射を左 Hom の標準同型で移した写像。 -/
def dgCoslicePrecomposeLeftMap :
    pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ⟶
      pinchedHomLeft (X := dgNerve R D) (Simplex.vertex q) (Simplex.vertex y) :=
  (pinchedLeftCosliceFiberIso (X := dgNerve R D)
    (Simplex.vertex (A := R) x) (Simplex.vertex y)).hom ≫
    dgCoslicePrecomposeFiber R D x q y s ≫
      (pinchedLeftCosliceFiberIso (X := dgNerve R D)
        (Simplex.vertex (A := R) q) (Simplex.vertex y)).inv
/-- 同じ左 Hom の写像も、元の同じ閉始点細分を全単体上で表す。 -/
lemma dgCoslicePrecomposeLeftMap_simplex {n : ℕ}
    (t : (pinchedHomLeft (X := dgNerve R D)
      (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    pinchedLeftSimplexVal n ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t) =
      dgCoslicePrecomposeCoordinate R D x q s
        (((pinchedLeftCosliceFiberIso (X := dgNerve R D)
          (Simplex.vertex x) (Simplex.vertex y)).hom.app _ t).val) := by
  let e := pinchedLeftCosliceFiberIso (X := dgNerve R D)
    (Simplex.vertex (A := R) q) (Simplex.vertex y)
  have hm : e.hom.app _ ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t) =
      (dgCoslicePrecomposeFiber R D x q y s).app _
        ((pinchedLeftCosliceFiberIso (X := dgNerve R D)
          (Simplex.vertex x) (Simplex.vertex y)).hom.app _ t) := by
    change e.hom.app _ (e.inv.app _ _) = _
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id _) _
  erw [← dgLeftPinchedCosliceFiberIso_simplex (X := dgNerve R D)
    (Simplex.vertex (A := R) q) (Simplex.vertex y)
    ((dgCoslicePrecomposeLeftMap R D x q y s).app _ t)]
  change cosliceFiberSimplex n (e.hom.app _ _) = _
  rw [hm, dgCoslicePrecomposeFiber_simplex]
end SerrePositivity.InfinityCategories
