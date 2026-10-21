module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceFiber
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCoslicePostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.DGFiberTransportSquare
/-!
概要：同じ dg 関手の実 coslice 後合成が誘導する、標準端点での実 fiber 射を計算する。
方針：底の頂点表示を等式でそろえ、包含と全単体座標を同時に保存する。
規約：任意の dg 関手。使われ方：Hom 単位前合成と関手像の合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
/-- 底の頂点等式による fiber 輸送は、元の同じ全空間の単体を保つ。 -/
lemma dgVertexFiberEqTransport_val {E B : SSet.{w}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (h : a = b) {n : ℕ} (t : (vertexFiber p a) _⦋n⦌) :
    ((eqToHom (congrArg (vertexFiber p) h)).app _ t).val = t.val := by
  subst b
  rfl
/-- 同じ頂点等式による fiber 輸送は、元の全空間への包含を保つ。 -/
lemma dgVertexFiberEqTransport_ι {E B : SSet.{w}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (h : a = b) : eqToHom (congrArg (vertexFiber p) h) ≫ vertexFiberι p b =
      vertexFiberι p a := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]
variable (R : Type u) [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  (F : DGFunctor R D E) (x y : D)
/-- 同じ dg 関手の実 coslice 写像の fiber 射を標準終点へ正規化する。 -/
def dgFunctorCosliceFiber :
    vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex x))) (Simplex.vertex y) ⟶
    vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R E)).symm
      (Simplex.vertex (F.obj x)))) (Simplex.vertex (F.obj y)) :=
  transportSquareFiberMap _ _ (dgFunctorCoslicePostcomp R F x) (dgNerve.map F)
    (dgFunctorCoslicePostcomp_projection R F x) (Simplex.vertex y) ≫
      eqToHom (congrArg (vertexFiber (sliceUnderProjection
        ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex (F.obj x)))))
          (dgFunctorNerve_vertex F y))
/-- 同じ実 fiber 射は、元の実 coslice 全体への包含と可換。 -/
lemma dgFunctorCosliceFiber_ι :
    dgFunctorCosliceFiber R F x y ≫
      vertexFiberι (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R E)).symm
        (Simplex.vertex (F.obj x)))) (Simplex.vertex (F.obj y)) =
      vertexFiberι (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
        (Simplex.vertex x))) (Simplex.vertex y) ≫ dgFunctorCoslicePostcomp R F x := by
  rw [dgFunctorCosliceFiber, Category.assoc,
    dgVertexFiberEqTransport_ι _ (dgFunctorNerve_vertex F y), transportSquareFiberMap_ι]
/-- 同じ実 fiber 射の全単体座標は、元の同じ dg 関手像。 -/
lemma dgFunctorCosliceFiber_simplex {n : ℕ}
    (t : (vertexFiber (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm
      (Simplex.vertex x))) (Simplex.vertex y)) _⦋n⦌) :
    cosliceFiberSimplex n ((dgFunctorCosliceFiber R F x y).app _ t) =
      (cosliceFiberSimplex n t).map F := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((eqToHom (congrArg (vertexFiber (sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex (F.obj x)))))
        (dgFunctorNerve_vertex F y))).app _ _).val.val) = _
  rw [dgVertexFiberEqTransport_val _ (dgFunctorNerve_vertex F y)]
  change SSet.yonedaEquiv (dgPointCosliceSimplex _
    ((dgFunctorCoslicePostcomp R F x).app _ t.val)) = _
  rw [dgFunctorCoslicePostcomp_coordinate, SSet.yonedaEquiv_comp]
  rfl
/-- 同じ実 fiber 射を標準左 Hom の同型で移したもの。 -/
def dgFunctorCosliceLeftMap :
    pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ⟶
    pinchedHomLeft (X := dgNerve R E) (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y)) :=
  (pinchedLeftCosliceFiberIso (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)).hom ≫
    dgFunctorCosliceFiber R F x y ≫
      (pinchedLeftCosliceFiberIso (X := dgNerve R E)
        (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y))).inv
/-- 同じ左 Hom の写像も、元の同じ全単体の dg 関手像を保つ。 -/
lemma dgFunctorCosliceLeftMap_simplex {n : ℕ}
    (t : (pinchedHomLeft (X := dgNerve R D)
      (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    pinchedLeftSimplexVal n ((dgFunctorCosliceLeftMap R F x y).app _ t) =
      (pinchedLeftSimplexVal n t).map F := by
  let e := pinchedLeftCosliceFiberIso (X := dgNerve R E)
    (Simplex.vertex (A := R) (F.obj x)) (Simplex.vertex (F.obj y))
  have hm : e.hom.app _ ((dgFunctorCosliceLeftMap R F x y).app _ t) =
      (dgFunctorCosliceFiber R F x y).app _
        ((pinchedLeftCosliceFiberIso (X := dgNerve R D)
          (Simplex.vertex x) (Simplex.vertex y)).hom.app _ t) := by
    change e.hom.app _ (e.inv.app _ _) = _
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id _) _
  calc
    _ = cosliceFiberSimplex n (e.hom.app _ _) :=
      (dgLeftPinchedCosliceFiberIso_simplex (X := dgNerve R E)
        (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y)) _).symm
    _ = _ := by rw [hm, dgFunctorCosliceFiber_simplex, dgLeftPinchedCosliceFiberIso_simplex]
end SerrePositivity.InfinityCategories
