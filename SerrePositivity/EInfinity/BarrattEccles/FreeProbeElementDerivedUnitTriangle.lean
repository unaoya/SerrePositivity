module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementUnitColumn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransComposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDerivedRoof
/-! 概要：元の全要素圏で自由単位と忘却後の実屋根の導来三角形を作る。
方針：元の二つの自然変換正方形を全 D(R) 関手圏へ送る。
規約：同じ単位・augmentation・評価と全パラメータを保持する。
使われ方：標準単位誘導射と元の実弱 Hom span の比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)

/-- 概要：元の単位と augmentation の全 D(R) 正方形。
方針：同じ全自然変換正方形を導来像へ送る。
規約：元の全添字を保持。使われ方：屋根の左脚比較。 -/
lemma freeProbeElementUnitColumn_derived_augmentation :
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A (freeProbeElementUnitColumn A X B) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
        (Functor.whiskerRight (freeProbeElementColumnAugmentation A X B)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))) =
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
        ((Functor.const (freeProbeElementIndex A X B)).map
          ((operad A).freeAlgebraAdjunction.unit.app
            ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))) :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom_square A _ _ _ _
    (freeProbeElementUnitColumn_augmentation A X B)

/-- 概要：元の単位と評価の全 D(R) 正方形。
方針：同じ随伴評価公式を全自然変換の導来像へ送る。
規約：元の標的置換を保持。使われ方：屋根の右脚比較。 -/
lemma freeProbeElementUnitColumn_derived_evaluation :
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A (freeProbeElementUnitColumn A X B) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
        (Functor.whiskerRight (freeProbeElementColumnEvaluation A X B)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))) =
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
        ((Functor.const (freeProbeElementIndex A X B)).map
          (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.carrier)) :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom_square A _ _ _ _
    (freeProbeElementUnitColumn_evaluation A X B)

/-- 概要：自由列の底の元の全 augmentation は全導来関手同型。
方針：元の全弱同値成分を同じ底の準同型として使う。
規約：元の自然変換自身を使う。使われ方：忘却後の全実屋根。 -/
def freeProbeElementUnderlyingAugmentationIso :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransIso A
    (Functor.whiskerRight (freeProbeElementColumnAugmentation A X B)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)))
    (fun s => freeProbeElementColumnAugmentation_weak A X B s)

/-- 概要：元の自由列を忘却した全 D(R) 屋根。
方針：同じ augmentation の逆と元の評価を合成する。
規約：元の全要素圏を保持。使われ方：標準単位の全族比較。 -/
def freeProbeElementUnderlyingRoof :=
  (freeProbeElementUnderlyingAugmentationIso A X B).inv ≫
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
      (Functor.whiskerRight (freeProbeElementColumnEvaluation A X B)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)))

/-- 概要：同じ元の単位の全族前合成は元の正規化実屋根を回収する。
方針：全 augmentation を反転し、同じ二つの導来正方形を接続する。
規約：点ごとの比較に縮めず同じ全関手圏で比較する。
使われ方：実 U の標準単位比較自身の弱同値性の判定。 -/
lemma freeProbeElementUnderlyingRoof_unit_triangle :
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
      ((Functor.const (freeProbeElementIndex A X B)).map
        ((operad A).freeAlgebraAdjunction.unit.app
          ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))) ≫
      freeProbeElementUnderlyingRoof A X B =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
        ((Functor.const (freeProbeElementIndex A X B)).map
          (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.carrier)) := by
  let e := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A
    ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc]
  change (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val) ≫ _) ≫ _ = _
  rw [← freeProbeElementUnitColumn_derived_augmentation A X B]
  have hfree : _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
      (Functor.whiskerRight (freeProbeElementColumnAugmentation A X B)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))) =
      (freeProbeElementUnderlyingAugmentationIso A X B).hom := rfl
  rw [hfree]
  simp only [freeProbeElementUnderlyingRoof, Category.assoc, Iso.hom_inv_id_assoc]
  rw [freeProbeElementUnitColumn_derived_evaluation A X B]
  simp only [e, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
