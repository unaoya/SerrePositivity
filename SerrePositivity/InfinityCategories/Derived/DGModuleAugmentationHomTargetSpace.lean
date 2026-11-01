module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationUnlifted
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetQuasiIsoInversion
public import SerrePositivity.InfinityCategories.Core.UniverseHomotopy
/-!
概要：実 augmentation の全単体族を射影的試験加群からの空間値 Hom の全関手同型へ送る。
方針：同じ閉辺・coslice 輸送と実入力切断の厳密等式を使う。
規約：生の出力の射影性は不要。使われ方：一般 kernel の完全性の Hom 試験。
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
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (T : RightModule R E)
/-- 同じ augmentation による全単体的な Hom 比較。 -/
def dgModuleAugmentationHomTargetSpaceHomotopy :
    SSet.Homotopy
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationSource R C E F)) ≫
          dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationTarget R C E F)) ≫
          dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T) :=
  functorHomotopyPostcomp
    (DoldKanComparison.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (dgModuleAugmentationUnliftedHomotopy R C E F))
    (dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T)
/-- 同じ augmentation による全単体的な Hom 比較。 -/
lemma dgModuleAugmentationHomTargetSpaceHomotopy_vertex_edge
    (X : DGModuleFunctorResolutionObject R C E F) :
    (simplicialHomotopyVertexEdge (dgModuleAugmentationHomTargetSpaceHomotopy R C E F T)
      (ULift.up (Simplex.vertex X))).edge =
    (dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T).app (Opposite.op ⦋1⦌)
      (ULift.up (dgClosedEdge R (RightModule R E) X.augmentation).edge) := by
  change (dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T).app (Opposite.op ⦋1⦌)
    (ULift.up (simplicialHomotopyVertexEdge
      (dgModuleAugmentationUnliftedHomotopy R C E F) (Simplex.vertex X)).edge) = _
  rw [dgModuleAugmentationUnliftedHomotopy_vertex_edge]
/-- 同じ augmentation による全単体的な Hom 比較。 -/
lemma dgModuleAugmentationHomTargetSpaceHomotopy_vertex_isInvertible
    (hT : moduleHomotopicallyProjective R E (ForgetEnrichment.of (Complex R) T))
    (X : DGModuleFunctorResolutionObject R C E F) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge
      (dgModuleAugmentationHomTargetSpaceHomotopy R C E F T)
      (ULift.up (Simplex.vertex X))).toTruncated := by
  let e := (SSet.Edge.ofTruncated
    (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
      (dgClosedEdge R (RightModule R E) X.augmentation))).map
        (dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T)
  have hInv : IsInvertibleEdge e :=
    dgModuleHomTargetUnderlyingSpaceInfinity_invertsQuasiIso R E T hT X.augmentation X.quasiIso
  have he : (simplicialHomotopyVertexEdge
      (dgModuleAugmentationHomTargetSpaceHomotopy R C E F T)
      (ULift.up (Simplex.vertex X))).edge = e.edge := by
    rw [dgModuleAugmentationHomTargetSpaceHomotopy_vertex_edge]
    rfl
  exact (isInvertibleEdge_congr (e := (simplicialHomotopyVertexEdge
    (dgModuleAugmentationHomTargetSpaceHomotopy R C E F T)
    (ULift.up (Simplex.vertex X))).toTruncated) (f := e.toTruncated) he).mpr hInv
/-- 同じ augmentation による全単体的な Hom 比較。 -/
def dgModuleAugmentationHomTargetSpaceIso
    (hT : moduleHomotopicallyProjective R E (ForgetEnrichment.of (Complex R) T)) :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationSource R C E F)) ≫
          dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationTarget R C E F)) ≫
          dgHomTargetUnderlyingSpaceInfinity R (RightModule R E) T) :=
  functorIsoOfPointwiseInvertibleHomotopy
    (dgModuleAugmentationHomTargetSpaceHomotopy R C E F T) (by
      rintro ⟨s⟩
      obtain ⟨X, rfl⟩ := (Simplex.vertexEquiv (A := R)
        (D := DGModuleFunctorResolutionObject R C E F)).symm.surjective s
      exact dgModuleAugmentationHomTargetSpaceHomotopy_vertex_isInvertible R C E F T hT X)
end SerrePositivity.InfinityCategories
