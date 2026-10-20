module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientLocalizingEdges
public import SerrePositivity.InfinityCategories.Stable.CofiberEdgesFullyFaithful
/-!
概要：cell 増大の実 nerve は分解上の Verdier 辺を元の Verdier 辺へ送る。
方針：完全充満忠実関手による実安定閉包の比較と指定対象像の厳密一致を使う。
規約：全実辺の条件。使われ方：平坦分解後の商の全局所化普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
omit [IsDGPretriangulated A D] in
/-- 分解上の指定実頂点の増大像は、元の指定実頂点全体と一致する。 -/
lemma dgCellAugmentation_nullVertex_image (P : Set D) :
    (dgNerve.map (DGCategoryCellResolution.augmentation A D)).app (Opposite.op ⦋0⦌) ''
      (Simplex.vertex '' resolvedDGNullObjects A D P) = Simplex.vertex '' P := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(DGCategoryCellResolution.augmentation A D).obj x, hx,
      (dgFunctorNerve_vertex _ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let a : DGCategoryCellResolution.Source A D := ⟨x⟩
    exact ⟨Simplex.vertex a, ⟨a, hx, rfl⟩, dgFunctorNerve_vertex _ a⟩
/-- 増大の実 nerve による、全実 Verdier 辺の所属の保存・反映。 -/
lemma dgCellAugmentation_verdierEdge_iff (P : Set D)
    (a : (dgNerve A (DGCategoryCellResolution.Source A D)) _⦋1⦌) :
    (dgNerve.map (DGCategoryCellResolution.augmentation A D)).app (Opposite.op ⦋1⦌) a ∈
      dgVerdierEdges A D P ↔ a ∈ dgVerdierEdges A (DGCategoryCellResolution.Source A D)
        (resolvedDGNullObjects A D P) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  let := dgNerve_isStable_of_pretriangulated A (DGCategoryCellResolution.Source A D)
  let := dgNerve_isStable_of_pretriangulated A D
  let E := dgNerve.map (DGCategoryCellResolution.augmentation A D)
  have : IsExactFunctor E :=
    isExactFunctor_of_isQCatEquivalence (dgCellAugmentationNerve_isQCatEquivalence A D)
  have hh := cofiberStableEdges_map_iff E
    (dgCellAugmentationNerve_isQCatEquivalence A D).isFullyFaithful
    (Simplex.vertex '' resolvedDGNullObjects A D P) (edgeOfSimplex a)
  rw [dgCellAugmentation_nullVertex_image A D P] at hh
  exact hh
/-- 元の実 Verdier 辺を反転する任意関手は、増大への制限で分解上の実 Verdier 辺を反転。 -/
lemma dgCellAugmentation_precomp_inverts (P : Set D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    InvertsEdges (dgNerve.map (DGCategoryCellResolution.augmentation A D) ≫ F)
      (dgVerdierEdges A (DGCategoryCellResolution.Source A D) (resolvedDGNullObjects A D P)) := by
  intro a ha
  let E := dgNerve.map (DGCategoryCellResolution.augmentation A D)
  have hb := hF ((dgCellAugmentation_verdierEdge_iff A D P a).mpr ha)
  exact (isInvertibleEdge_congr
    (e := (edgeOfSimplex (E.app (Opposite.op ⦋1⦌) a)).map ((truncation 2).map F))
    (f := (edgeOfSimplex a).map ((truncation 2).map (E ≫ F))) rfl).mp hb
end SerrePositivity.InfinityCategories
