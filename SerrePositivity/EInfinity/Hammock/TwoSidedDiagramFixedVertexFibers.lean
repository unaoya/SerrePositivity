module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramFixedVertices
public import SerrePositivity.EInfinity.Hammock.IndexedSum
/-!
# 固定頂点列ごとの元の部分対角

概要：元の部分対角は固定頂点列ごとの隣接 Hom と両ラベルの単体集合の和と同型。
方針：同じ元の射列の全単射と端点等式を使う。
規約：全作用素と長さ零を保持する。
使われ方：DK10.6(ii)の元の固定頂点列ごとの因子の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
open CategoryTheory
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}) {O : Type u}
  (p : (n : SimplexCategoryᵒᵖ) → O ≃ (D.obj n).base)
  (hp : ∀ {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (o : O),
    (D.map θ).base.obj (p n o) = p m o)
  (k : SimplexCategoryᵒᵖ) (x : Fin (k.unop.len + 1) → O)

def fiberSpace : SSet.{u} where
  obj n := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates.Fiber (p n) (leftLabels D n) (rightLabels D n) k.unop.len x
  map θ := ↾fun v => (map D p hp k θ ⟨x, v⟩).2
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro v
    have h := (space D p hp k).map_id_apply n (⟨x, v⟩)
    exact eq_of_heq (Sigma.mk.inj h).2
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro v
    have h := (space D p hp k).map_comp_apply θ φ (⟨x, v⟩)
    exact eq_of_heq (Sigma.mk.inj h).2

def sumIso : space D p hp k ≅ IndexedSum.space (fiberSpace D p hp k) := Iso.refl _

def chainRowIso : chainRow D k ≅ IndexedSum.space (fiberSpace D p hp k) :=
  iso D p hp k ≪≫ sumIso D p hp k

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram.FixedVertices
