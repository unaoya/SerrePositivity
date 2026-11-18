module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedHomFrames
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorHomBifunctor

/-!
# 元の自由単位と同じ正規化 Hom 比較の厳密な全次数公式

概要：自由像の随伴 Hom 同型は元の単位の前合成であり、全 augmentation と可換。
方針：同じ自由随伴の全自然 Hom 同値を実正規化フレームで評価する。
規約：元の単位・元の標的代数・全単体次数を保持する。
使われ方：標準単位誘導射と実 DK Hom の全比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma freeNormalizedProbeHomAdjunctionIso_apply (X : Complex A) (B : (operad A).Algebra)
    (n : SimplexCategory) (f : ((freeNormalizedProbeFrame A).obj X).obj n ⟶ B) :
    ((((freeNormalizedProbeHomAdjunctionIso A).hom.app (Opposite.op X)).app B).app
      (Opposite.op n)) f =
    (operad A).freeAlgebraAdjunction.unit.app
      (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X).obj n) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map f := by
  change (operad A).freeAlgebraAdjunction.homEquiv _ _ f = _
  exact (operad A).freeAlgebraAdjunction.homEquiv_unit _ _ f

lemma freeNormalizedProbeHomAdjunctionIso_augmentation
    (X : Complex A) (B : (operad A).Algebra) (n : SimplexCategory)
    (f : (freeProbeFunctor A).obj X ⟶ B) :
    ((((freeNormalizedProbeHomAdjunctionIso A).hom.app (Opposite.op X)).app B).app
      (Opposite.op n)) (((freeNormalizedProbeAugmentation A).app X).app n ≫ f) =
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n ≫
      (operad A).freeAlgebraAdjunction.unit.app ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map f := by
  change (operad A).freeAlgebraAdjunction.homEquiv _ _
    ((operad A).freeAlgebraFunctor.map _ ≫ f) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]

def freeNormalizedProbeDoldKanIso :
    freeNormalizedProbeHom A ≅
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).op ⋙
        _root_.SerrePositivity.ComplexLimits.actualDoldKanHomBifunctor A) ⋙
        (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) :=
  freeNormalizedProbeHomAdjunctionIso A ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).op
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorHomDoldKanIso A))
      ((Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)))

lemma freeNormalizedProbeDoldKanIso_apply (X : Complex A) (B : (operad A).Algebra)
    (n : SimplexCategory) (f : ((freeNormalizedProbeFrame A).obj X).obj n ⟶ B) :
    ((((freeNormalizedProbeDoldKanIso A).hom.app (Opposite.op X)).app B).app
      (Opposite.op n)) f =
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) B.carrier n
      ((operad A).freeAlgebraAdjunction.unit.app
        (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X).obj n) ≫
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map f) := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A _ _ n
    (((((freeNormalizedProbeHomAdjunctionIso A).hom.app (Opposite.op X)).app B).app
      (Opposite.op n)) f) = _
  rw [freeNormalizedProbeHomAdjunctionIso_apply]
  rfl

lemma freeNormalizedProbeDoldKanIso_augmentation
    (X : Complex A) (B : (operad A).Algebra) (n : SimplexCategory)
    (f : (freeProbeFunctor A).obj X ⟶ B) :
    ((((freeNormalizedProbeDoldKanIso A).hom.app (Opposite.op X)).app B).app
      (Opposite.op n)) (((freeNormalizedProbeAugmentation A).app X).app n ≫ f) =
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) B.carrier n
      (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X).app n ≫
        (operad A).freeAlgebraAdjunction.unit.app
          ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) ≫
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).map f) := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A _ _ n
    (((((freeNormalizedProbeHomAdjunctionIso A).hom.app (Opposite.op X)).app B).app
      (Opposite.op n)) _) = _
  rw [freeNormalizedProbeHomAdjunctionIso_augmentation]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
