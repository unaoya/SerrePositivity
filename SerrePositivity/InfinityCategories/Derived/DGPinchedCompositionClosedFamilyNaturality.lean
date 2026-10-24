module
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyGeneral
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexNaturality
/-!
概要：coherent 合成 prism の自然性を両側の指定閉射に適用する。
方針：任意族の二入力自然性を、閉頂点の定値族とその dg 関手像へ制限する。
規約：Small 仮定なしで全パラメーター・全時刻と端点輸送を保持する。
使われ方：D2 の閉前合成・閉後合成の coherent prism の係数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]

lemma dgPinchedCompositionFamilyPrism_closed_first_naturality (Q : DGFunctor A D E)
    {K : SSet.{max u v}} {x y z : D}
    (r : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (g : K ⟶ DGNerve.pinchedHom A D y z)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex z) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj z)) :=
        dgPinchedCompositionTargetPoint_naturality A D E Q z) :
    dgPinchedCompositionFamilyPrism A D (SSet.const (pinchedClosedVertex A D r)) g ≫
      sliceOverPostcomp _ (dgNerve.map Q) ≫ (eqToIso (congrArg sliceOver hp)).hom =
    dgPinchedCompositionFamilyPrism A E
      (SSet.const (pinchedClosedVertex A E (Q.onClosed.map r)))
      (g ≫ pinchedHomChainMap (Q.map y z)) := by
  simpa only [SSet.const_comp, pinchedClosedVertex_map] using
    dgPinchedCompositionFamilyPrism_naturality A D E Q
      (SSet.const (pinchedClosedVertex A D r)) g hp

lemma dgPinchedCompositionFamilyPrism_closed_second_naturality (Q : DGFunctor A D E)
    {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y)
    (r : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex z) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj z)) :=
        dgPinchedCompositionTargetPoint_naturality A D E Q z) :
    dgPinchedCompositionFamilyPrism A D f (SSet.const (pinchedClosedVertex A D r)) ≫
      sliceOverPostcomp _ (dgNerve.map Q) ≫ (eqToIso (congrArg sliceOver hp)).hom =
    dgPinchedCompositionFamilyPrism A E (f ≫ pinchedHomChainMap (Q.map x y))
      (SSet.const (pinchedClosedVertex A E (Q.onClosed.map r))) := by
  simpa only [SSet.const_comp, pinchedClosedVertex_map] using
    dgPinchedCompositionFamilyPrism_naturality A D E Q
      f (SSet.const (pinchedClosedVertex A D r)) hp
end SerrePositivity.InfinityCategories
