module

public import SerrePositivity.EInfinity.Hammock.TransfunctorTwoSidedDiagram

/-!
# 元の両 transfunctor の自然変換の二方向図式への作用

概要：元の係数の自然変換は、全次数の二方向図式の元の自然変換を与える。
方針：各 fiber に制限し、元の Grothendieck 圏の標準射への自然性を使う。
規約：底の関手は元の恒等関手で、両係数の元の成分を保持する。
使われ方：DK10.4の元の係数比較の全作用素。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.Transfunctor
open CategoryTheory Opposite
variable {I : Type v} [Category I] {B : I ⥤ Cat.{u, u}}
  {L L' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant (B ⋙ Cat.opFunctor)} {R R' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant B}

def fiberMap {T T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant B} (τ : T ⟶ T') (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.fiber T i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.fiber T' i :=
  Functor.whiskerLeft (Grothendieck.ι B i) τ

def twoSidedDiagramMap (α : L ⟶ L') (β : R ⟶ R') :
    twoSidedDiagram B L R ⟶ twoSidedDiagram B L' R' where
  app i := ⟨𝟭 _, fiberMap α i, fiberMap β i⟩
  naturality i j θ := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ rfl ?_ ?_
    · apply heq_of_eq
      apply NatTrans.ext
      funext w
      exact α.naturality ((Grothendieck.ιNatTrans (F := B ⋙ Cat.opFunctor) θ).app w)
    · apply heq_of_eq
      apply NatTrans.ext
      funext w
      exact β.naturality ((Grothendieck.ιNatTrans (F := B) θ).app w)

end SerrePositivity.EInfinity.Hammock.Transfunctor
