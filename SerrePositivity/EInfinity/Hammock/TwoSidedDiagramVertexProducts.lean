module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramFixedVertexFibers
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainTransport
public import SerrePositivity.EInfinity.Hammock.FiniteProduct
public import SerrePositivity.EInfinity.Hammock.IndexedSumIso
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom
/-!
# 元の部分対角の固定頂点列ごとの有限 Hom 積

概要：元の chainRow を固定頂点列ごとの隣接 Hom と両端係数の直積の和へ戻す。
方針：元の対象表示・係数 transfunctor の評価を使い、全因子の移送を照合する。
規約：同型は元の全単体と全作用素を保持し、長さ零も含む。
使われ方：DK10.6(ii)の元の有限直積の和による弱不変性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
open CategoryTheory Opposite MonoidalCategory
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}) {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)

def homSpace (X Y : O) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor) (fun n o => p n o) hp X Y

def leftSpace (X : O) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.objectDiagram (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor ⋙ Cat.opFunctor)
      (fun n => op (p n X)) (fun θ => congrArg op (hp θ X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.leftTransfunctor D) ⋙ nerveFunctor)

def rightSpace (X : O) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.objectDiagram (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.baseFunctor)
      (fun n => p n X) (fun θ => hp θ X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor.rightTransfunctor D) ⋙ nerveFunctor)

def product (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) : SSet.{u} :=
  FiniteProduct.space (fun i : Fin k.unop.len => homSpace D p hp (x i.castSucc) (x i.succ)) ⊗
    (leftSpace D p hp (x (Fin.last k.unop.len)) ⊗ rightSpace D p hp (x 0))

def productIso (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    fiberSpace D p hp k x ≅ product D p hp k x :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap (p m) (D.map θ).base
      (leftLabelsMap D θ) (rightLabelsMap D θ) (hp θ) x v = _
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cast_fiber (leftLabels D m) (rightLabels D m)
      (fun i => hp θ (x i))]
    rfl)

def productsIso (k : SimplexCategoryᵒᵖ) :
    chainRow D k ≅ IndexedSum.space (product D p hp k) :=
  chainRowIso D p hp k ≪≫ IndexedSum.mapIso (productIso D p hp k)

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
