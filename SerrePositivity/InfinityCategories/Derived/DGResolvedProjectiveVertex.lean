module
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveAugmentationHom
/-!
概要：同じ resolved augmentation の頂点辺の可逆性を個々の射影的出力から検出する。
方針：元の augmentation の準同型性と、半自由出力の射影性を使う。
規約：全出力の射影性は要求しない。使われ方：半自由入力上の変形円柱の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 射影的な同じ出力に対する resolved augmentation の実頂点辺は可逆。 -/
lemma dgModuleResolvedAugmentationHomotopy_projective_vertex_isInvertible (x : C)
    (hx : dgModuleProjectiveProperty R E (F.obj x)) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge
      (dgModuleResolvedAugmentationHomotopy R C E F) (Simplex.vertex x)).toTruncated := by
  let Q := dgModuleOutputResolutionObject R C E F x
  have hQ : dgModuleProjectiveProperty R E (F.obj Q.source) := by
    rw [dgModuleOutputResolutionObject_source R C E F x]
    exact hx
  have := dgModuleEdge_isIso_of_homotopy R E Q.augmentation
    (moduleHomotopicallyProjective_quasiIso_isIso_homotopy R E
      (dgSemifreeModule_isProjective R E Q.replacement) hQ Q.augmentation Q.quasiIso)
  have he : IsInvertibleEdge (X := dgModuleNerve R E)
      (dgClosedEdge R (RightModule R E) Q.augmentation) :=
    (edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge R E Q.augmentation).toTruncated)
  exact (isInvertibleEdge_congr
    (dgModuleResolvedAugmentationHomotopy_vertex_edge R C E F x)).mpr he
end SerrePositivity.InfinityCategories
