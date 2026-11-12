module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonalLabels
/-!
# 元の部分対角の固定頂点表示

概要：元の chainRow を固定頂点列と隣接 Hom・両ラベルで表す単体集合へ厳密に戻す。
方針：元の全作用素と同じ端点移送を使い、既存の関手則へ回収する。
規約：元の全単体を保持し、弱同値性を入力にしない。
使われ方：DK10.6(ii)の固定頂点列ごとの Hom 因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
open CategoryTheory Opposite
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}) {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)
  (k : SimplexCategoryᵒᵖ)

abbrev factors (n : SimplexCategoryᵒᵖ) :=
  Σ x : Fin (k.unop.len + 1) → O,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.Fiber (p n) (leftLabels D n) (rightLabels D n) k.unop.len x

def degreeEquiv (n : SimplexCategoryᵒᵖ) : (chainRow D k).obj n ≃ factors D p k n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.equivalence (p n) (leftLabels D n) (rightLabels D n) k.unop.len

def map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (e : factors D p k n) : factors D p k m :=
  ⟨e.1, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap (p m) (D.map θ).base
    (leftLabelsMap D θ) (rightLabelsMap D θ) (hp θ) e.1 e.2⟩

lemma degreeEquiv_symm_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (e : factors D p k n) :
    (degreeEquiv D p k m).symm (map D p hp k θ e) =
      (chainRow D k).map θ ((degreeEquiv D p k n).symm e) := by
  rcases e with ⟨x, v⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode (p m) _ _ _ x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.fiberMap (p m) (D.map θ).base
      (leftLabelsMap D θ) (rightLabelsMap D θ) (hp θ) x v) =
    (chainRow D k).map θ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode (p n) _ _ _ x v)
  rw [chainRow_map]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.decode_naturality (p m) (D.map θ).base
    (leftLabelsMap D θ) (rightLabelsMap D θ) (hp θ) x v).symm

def space : SSet.{u} where
  obj n := factors D p k n
  map θ := ↾(map D p hp k θ)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro e
    apply (degreeEquiv D p k n).symm.injective
    change (degreeEquiv D p k n).symm (map D p hp k (𝟙 n) e) =
      (degreeEquiv D p k n).symm e
    rw [degreeEquiv_symm_map]
    exact (chainRow D k).map_id_apply n _
  map_comp {n m l} θ φ := by
    apply ConcreteCategory.hom_ext
    intro e
    apply (degreeEquiv D p k l).symm.injective
    change (degreeEquiv D p k l).symm (map D p hp k (θ ≫ φ) e) =
      (degreeEquiv D p k l).symm (map D p hp k φ (map D p hp k θ e))
    rw [degreeEquiv_symm_map, degreeEquiv_symm_map, degreeEquiv_symm_map]
    exact (chainRow D k).map_comp_apply θ φ _

def iso : chainRow D k ≅ space D p hp k :=
  NatIso.ofComponents (fun n => Equiv.toIso (degreeEquiv D p k n)) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro e
    apply (degreeEquiv D p k m).symm.injective
    change (degreeEquiv D p k m).symm ((degreeEquiv D p k m) ((chainRow D k).map θ e)) =
      (degreeEquiv D p k m).symm (map D p hp k θ ((degreeEquiv D p k n) e))
    rw [Equiv.symm_apply_apply, degreeEquiv_symm_map, Equiv.symm_apply_apply])

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
