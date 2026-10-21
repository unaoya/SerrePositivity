module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverNerveFiber

/-!
# 元の全語の graph の fiber と nerve の図式の同型

概要：各語の元の fiber の同定は全語の作用にも自然である。
方針：元の全部分圏の包含と同じ単体を回収する。
規約：元の全語と全単体作用素の二方向を同時に保持する。
使われ方：元の hammock 上の値の fiber への余極限比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def fiberValueDiagramIso : fiberGraphDiagram A Y β ≅
    SimplicialLabelledColimit.fiberDiagram (graphValueLabels A Y) β :=
  NatIso.ofComponents (fiberGraphIso A Y β) (by
    intro a b f
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    rfl)

lemma fiberValueDiagramIso_hom_inclusion (w : Word) :
    (fiberValueDiagramIso A Y β).hom.app w ≫
      SimplicialValueFiber.inclusion (graphValue A Y w) β =
        nerveMap (zigzagValueProperty A w Y β).ι := rfl

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
