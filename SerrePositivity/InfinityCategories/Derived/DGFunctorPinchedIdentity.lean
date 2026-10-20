module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedIdentityFamily
/-!
概要：dg 関手の実 Hom 鎖写像が、標準 dg 頂点の実恒等 pinched 頂点を保つことを証明する。
方針：実 nerve の関手性と端点輸送付きの鎖写像の同定を使う。
規約：実恒等一次単体を保持する。使われ方：商 Hom 作用の単位族の識別。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
/-- dg 関手の実 Hom 鎖写像は、標準頂点の実恒等 pinched 頂点を厳密に保つ。 -/
lemma dgFunctorPinchedMap_identityVertex {A : Type u} [CommRing A] {D E : Type v}
    [DGCategory A D] [DGCategory A E] (F : DGFunctor A D E) (x : D) :
    (pinchedHomChainMap (F.map x x)).app (Opposite.op ⦋0⦌)
      (pinchedIdentityVertex (X := dgNerve A D) (Simplex.vertex x)) =
        pinchedIdentityVertex (X := dgNerve A E) (Simplex.vertex (F.obj x)) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (pinchedIdentityVertex (X := dgNerve A D) (Simplex.vertex x)))
      (dgFunctor_pinchedHomMap_eq F x x)
  exact h.symm.trans
    ((congrArg (fun a => (pinchedEndpointIso (dgFunctorNerve_vertex F x)
      (dgFunctorNerve_vertex F x)).hom.app (Opposite.op ⦋0⦌) a)
        (pinchedHomMap_identityVertex (dgNerve.map F) (Simplex.vertex x))).trans
          (pinchedIdentityVertex_transport (dgFunctorNerve_vertex F x)))
end SerrePositivity.InfinityCategories
