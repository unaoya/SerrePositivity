module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedIdentityFamily
/-!
概要：dg 関手の実 Hom 鎖写像が、標準 dg 頂点の実恒等 pinched 頂点を保つことを証明する。
方針：実 nerve の関手性と端点輸送付きの鎖写像の同定を使う。
規約：実恒等一次単体を保持する。使われ方：商 Hom 作用の単位族の識別。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
/-- dg 関手の実 Hom 鎖写像は、標準頂点の実恒等 pinched 頂点を厳密に保つ。 -/
lemma dgFunctorPinchedMap_identityVertex {A : Type u} [CommRing A] {D E : Type v}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x x)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq F x x)
  exact h.symm.trans
    ((congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x)).hom.app (Opposite.op ⦋0⦌) a)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMap_identityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex_transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
