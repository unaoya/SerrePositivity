module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementDerivedUnitTriangle
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitAmbientComponent
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedConstantNatTrans
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementConstantRoof
/-!
概要：元の忘却屋根と自由単位の全三角形を同じ定値端点間で表す。
方針：既存の全屋根三角形の両端を輸送し、定値自然変換を回収する。
規約：元の単位成分・augmentation・全要素パラメータを保持する。
使われ方：実 U の全族公式と標準単位比較の弱同値判定の接合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)

/-- 概要：元の忘却屋根を同じ複体頂点の定値関手間に置く。
方針：既存の定値端点同型で元の屋根を輸送する。
規約：元の全屋根を保持。使われ方：標準単位の全族三角形。 -/
def freeProbeElementUnderlyingRoofFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom
    (nerve (freeProbeElementIndex A X B)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
    ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((freeProbeFunctor A).obj X).carrier))
    ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B.carrier)) :=
  (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (freeProbeElementIndex A X B)
    ((freeProbeFunctor A).obj X).carrier).inv ≫
    freeProbeElementUnderlyingRoof A X B ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (freeProbeElementIndex A X B) B.carrier).hom

/-- 概要：定値端点への輸送は元の忘却屋根と同じ全 Arrow を保つ。
方針：既存の定値端点等式を Arrow の等式判定へ渡す。
規約：元の屋根自身を保持。使われ方：相対列の忘却像の全族比較。 -/
lemma freeProbeElementUnderlyingRoofFamily_arrow :
    Arrow.mk (freeProbeElementUnderlyingRoofFamily A X B) =
      Arrow.mk (freeProbeElementUnderlyingRoof A X B) := by
  apply (Arrow.mk_eq_mk_iff _ _).mpr
  refine ⟨(congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstant_eq A (freeProbeElementIndex A X B)
      ((freeProbeFunctor A).obj X).carrier)).symm,
    (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstant_eq A (freeProbeElementIndex A X B) B.carrier)).symm, ?_⟩
  rfl

/-- 概要：同じ元の単位成分の定値族による前合成は元の複体屋根を回収する。
方針：元の全単位三角形と定値自然変換の全円柱比較を接続する。
規約：全 h Fun の同じ射の等式。使われ方：実単位比較の全族判定。 -/
lemma freeProbeElementUnderlyingRoofFamily_unit_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve (freeProbeElementIndex A X B))
      (freeProbeUnitOrdinaryHom A X) ≫ freeProbeElementUnderlyingRoofFamily A X B =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve (freeProbeElementIndex A X B))
        (Truncated.HomotopyCategory.homMk
          ((nerve.edgeMk (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.carrier)).map
            (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) := by
  rw [freeProbeUnitHom_component, ← _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom_const,
    ← _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom_const]
  dsimp only [freeProbeElementUnderlyingRoofFamily, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily]
  have he : _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (freeProbeElementIndex A X B)
      ((freeProbeFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).obj X) =
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (freeProbeElementIndex A X B)
        ((freeProbeFunctor A).obj X).carrier := rfl
  rw [he]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hu := freeProbeElementUnderlyingRoof_unit_triangle A X B
  change _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
    ((Functor.const (freeProbeElementIndex A X B)).map ((freeProbeUnitNatTrans A).app X)) ≫
      freeProbeElementUnderlyingRoof A X B = _ at hu
  rw [← Category.assoc
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A ((Functor.const (freeProbeElementIndex A X B)).map
      ((freeProbeUnitNatTrans A).app X))) (freeProbeElementUnderlyingRoof A X B)
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (freeProbeElementIndex A X B) B.carrier).hom,
    hu]
  simp only [Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
