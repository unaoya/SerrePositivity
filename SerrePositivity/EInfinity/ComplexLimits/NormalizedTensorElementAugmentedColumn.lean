module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveCoconePrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalCoconeSimplex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram

/-!
概要：元の frame augmentation の通常右余錐と、その各有限列の終端付き実図式を作る。
方針：元の混合宇宙の余錐を Hom 持ち上げし、既存の終端追加関手で同じ列へ制限する。
規約：対象・chain map・全合成を元の余錐から得る。使われ方：二重 cone の通常部分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementAugmentationCocone : Cocone (normalizedTensorElementDiagram A X Y) where
  pt := X
  ι := normalizedTensorElementAugmentation A X Y

def normalizedTensorElementLiftedAugmentationCocone :
    Cocone (FrameHom.MixedNerve.lifted (normalizedTensorElementDiagram A X Y)) :=
  FrameHom.MixedNerve.liftedCocone (normalizedTensorElementAugmentationCocone A X Y)

def normalizedTensorElementAugmentedColumn {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    ComposableArrows (Complex A) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram (normalizedTensorElementLiftedAugmentationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1}) ⋙ ULiftHom.down.{u, u + 1, u + 1}

lemma normalizedTensorElementAugmentedColumn_obj_castSucc {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    (normalizedTensorElementAugmentedColumn A X Y c).obj i.castSucc =
      (normalizedTensorElementDiagram A X Y).obj (c.obj i) := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (normalizedTensorElementLiftedAugmentationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1})).obj i.castSucc) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast]
  rfl

lemma normalizedTensorElementAugmentedColumn_obj_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorElementAugmentedColumn A X Y c).obj (Fin.last (n + 1)) = X := by
  change ULiftHom.objDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram
    (normalizedTensorElementLiftedAugmentationCocone A X Y)
    (c ⋙ ULiftHom.up.{u, u + 1, u + 1})).obj (Fin.last (n + 1))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
