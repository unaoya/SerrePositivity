module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationProjections
public import SerrePositivity.InfinityCategories.Derived.HomotopyPrecompVertex
/-!
概要：元の全関手の半自由出力分解から、同じ生の関手への実 augmentation を構成する。
方針：全 augmentation ホモトピーを同じ入力切断で引き戻し、両射影を照合する。
規約：入力の Small 性や元の出力の射影性は不要。使われ方：分解の局所化普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R C (RightModule R E))
/-- 半自由出力分解と実包含の合成から、元の同じ全関手への全単体ホモトピー。 -/
def dgModuleResolvedAugmentationHomotopy :
    SSet.Homotopy
      (dgModuleResolvedInfinity R C E F ≫
        dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)))
      (dgNerve.map F) := by
  let H := functorHomotopyPrecomp (dgModuleAugmentationUnliftedHomotopy R C E F)
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)
  exact { h := H.h
          h₀ := H.h₀.trans (by
            simpa only [Category.assoc] using!
              dgModuleResolvedSection_augmentationSource R C E F)
          h₁ := H.h₁.trans (by
            simpa only [Category.assoc] using!
              dgModuleResolvedSection_augmentationTarget R C E F)
          rel := H.rel }
/-- 同じ入力切断で選ばれた実 augmentation は、全単体比較の同じ頂点辺。 -/
lemma dgModuleResolvedAugmentationHomotopy_vertex_edge (x : C) :
    (simplicialHomotopyVertexEdge (dgModuleResolvedAugmentationHomotopy R C E F)
      (Simplex.vertex x)).edge =
      (dgClosedEdge R (RightModule R E)
        (dgModuleOutputResolutionObject R C E F x).augmentation).edge := by
  change (simplicialHomotopyVertexEdge
    (functorHomotopyPrecomp (dgModuleAugmentationUnliftedHomotopy R C E F)
      (dgNerve.map (dgUniverseLiftUp R C) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv))
    (Simplex.vertex x)).edge = _
  rw [simplicialHomotopyVertexEdge_precomp_edge]
  have hx : (dgNerve.map (dgUniverseLiftUp R C) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv).app
        (Opposite.op ⦋0⦌) (Simplex.vertex x) =
      Simplex.vertex (dgModuleOutputResolutionObject R C E F x) := by
    exact (Simplex.vertexEquiv (A := R)
      (D := DGModuleFunctorResolutionObject R C E F)).symm_apply_apply _ |>.symm
  rw [hx, dgModuleAugmentationUnliftedHomotopy_vertex_edge]
end SerrePositivity.InfinityCategories
