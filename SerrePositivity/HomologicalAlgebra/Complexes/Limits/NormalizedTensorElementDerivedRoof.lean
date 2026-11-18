module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDiagram
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransComponent

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementDerivedAugmentationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
    (nerveMap ((Functor.const (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).obj X) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransIso A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation_quasiIso A X Y)

def normalizedTensorElementDerivedEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
    (nerveMap ((Functor.const (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).obj Y) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y)

def normalizedTensorElementDerivedRoof :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (nerveMap ((Functor.const (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).obj X) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
    (nerveMap ((Functor.const (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)).obj Y) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).inv ≫
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y

lemma normalizedTensorElementDerivedAugmentationIso_hom :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).hom =
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y) := rfl

lemma normalizedTensorElementDerivedRoof_triangle :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).hom ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y := by
  simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof, Iso.hom_inv_id_assoc]

end SerrePositivity.ComplexLimits
