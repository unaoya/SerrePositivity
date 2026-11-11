module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransComponent

/-!
概要：全正規化単体の元の二つの自然変換を同じ既存 D(R) へ送る。
方針：同じ augmentation の全自然同型を反転し、同じ評価二胞体と合成する。
規約：反対要素圏の全図式と全円柱を保持する。
使われ方：元の正規化 Hom 全族と導来単位の大域三角形を照合する実屋根。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementDerivedAugmentationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (normalizedTensorElementDiagram A X Y) ≫
      complexOrdinaryDerivedSource A)
    (nerveMap ((Functor.const (normalizedTensorElementIndex A X Y)).obj X) ≫
      complexOrdinaryDerivedSource A) :=
  complexOrdinaryDerivedNatTransIso A (normalizedTensorElementAugmentation A X Y)
    (normalizedTensorElementAugmentation_quasiIso A X Y)

def normalizedTensorElementDerivedEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap (normalizedTensorElementDiagram A X Y) ≫
      complexOrdinaryDerivedSource A)
    (nerveMap ((Functor.const (normalizedTensorElementIndex A X Y)).obj Y) ≫
      complexOrdinaryDerivedSource A) :=
  complexOrdinaryDerivedNatTransHom A (normalizedTensorElementEvaluation A X Y)

def normalizedTensorElementDerivedRoof :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (nerveMap ((Functor.const (normalizedTensorElementIndex A X Y)).obj X) ≫
      complexOrdinaryDerivedSource A)
    (nerveMap ((Functor.const (normalizedTensorElementIndex A X Y)).obj Y) ≫
      complexOrdinaryDerivedSource A) :=
  (normalizedTensorElementDerivedAugmentationIso A X Y).inv ≫
    normalizedTensorElementDerivedEvaluation A X Y

lemma normalizedTensorElementDerivedAugmentationIso_hom :
    (normalizedTensorElementDerivedAugmentationIso A X Y).hom =
    complexOrdinaryDerivedNatTransHom A (normalizedTensorElementAugmentation A X Y) := rfl

lemma normalizedTensorElementDerivedRoof_triangle :
    (normalizedTensorElementDerivedAugmentationIso A X Y).hom ≫
      normalizedTensorElementDerivedRoof A X Y =
    normalizedTensorElementDerivedEvaluation A X Y := by
  simp only [normalizedTensorElementDerivedRoof, Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.ComplexLimits
