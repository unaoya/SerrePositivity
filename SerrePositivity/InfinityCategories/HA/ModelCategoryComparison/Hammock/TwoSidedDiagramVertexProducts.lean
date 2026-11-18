module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramFixedVertexFibers
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainTransport
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSumIso
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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
open _root_.CategoryTheory _root_.Opposite _root_.CategoryTheory.MonoidalCategory
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
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space (fun i : Fin k.unop.len => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.homSpace D p hp (x i.castSucc) (x i.succ)) ⊗
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.leftSpace D p hp (x (Fin.last k.unop.len)) ⊗ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.rightSpace D p hp (x 0))

def productIso (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.fiberSpace D p hp k x ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.product D p hp k x :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap (p m) (D.map θ).base
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabelsMap D θ) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabelsMap D θ) (hp θ) x v = _
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cast_fiber (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.leftLabels D m) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.rightLabels D m)
      (fun i => hp θ (x i))]
    rfl)

def productsIso (k : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.chainRow D k ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.product D p hp k) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.chainRowIso D p hp k ≪≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.mapIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.productIso D p hp k)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
