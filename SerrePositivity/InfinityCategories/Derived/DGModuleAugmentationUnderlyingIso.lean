module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingSpaceQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationClosedEdge
public import SerrePositivity.InfinityCategories.Core.UniverseHomotopy
/-!
概要：実分解圏上の同じ augmentation を、空間値全関手の比較同型へ昇格する。
方針：同じ実頂点辺の準同型性から像の可逆性を示し、全単体ホモトピー自身から同型を作る。
規約：半自由 Hom の始域と同じ共通対象宇宙を使い、元の出力に射影性を課さない。
使われ方：実 D(R) 値 Hom の augmentation の空間値比較同型。
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
  (F : DGFunctor R C (RightModule R PUnit.{1}))
/-- 同じ実 augmentation の全単体族を、R からの基礎空間関手へ送ったホモトピー。 -/
def dgModuleAugmentationUnderlyingSpaceHomotopy :
    SSet.Homotopy
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationSourceLift R C PUnit.{1} F)) ≫
          dgHomUnderlyingSpaceInfinity R C)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationTargetLift R C PUnit.{1} F)) ≫
          dgHomUnderlyingSpaceInfinity R C) :=
  functorHomotopyPostcomp
    (DoldKanComparison.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (dgModuleAugmentationNerveHomotopy R C PUnit.{1} F)) (dgHomUnderlyingSpaceInfinity R C)
/-- 同じ空間値ホモトピーの実頂点辺は、元の同じ実辺を持ち上げて写したもの。 -/
lemma dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_edge
    (X : DGModuleFunctorResolutionObject R C PUnit.{1} F) :
    (simplicialHomotopyVertexEdge (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (Simplex.vertex X))).edge =
    (dgHomUnderlyingSpaceInfinity R C).app (Opposite.op ⦋1⦌)
      (ULift.up (simplicialHomotopyVertexEdge (dgModuleAugmentationNerveHomotopy R C PUnit.{1} F)
        (Simplex.vertex X)).edge) := rfl
/-- 同じ空間値 augmentation の全ての実頂点成分は可逆。 -/
lemma dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_isInvertible
    (X : DGModuleFunctorResolutionObject R C PUnit.{1} F) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge
      (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (Simplex.vertex X))).toTruncated := by
  let e := (SSet.Edge.ofTruncated
    (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
      (dgClosedEdge R (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R
          (RightModule R PUnit.{1})).onClosed.map X.augmentation)))).map
      (dgHomUnderlyingSpaceInfinity R C)
  have hInv : IsInvertibleEdge e :=
    dgHomUnderlyingSpaceInfinity_invertsQuasiIso R C X.augmentation X.quasiIso
  have he : (simplicialHomotopyVertexEdge (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (Simplex.vertex X))).edge = e.edge := by
    rw [dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_edge,
      dgModuleAugmentationNerveHomotopy_vertex_edge]
    rfl
  exact (isInvertibleEdge_congr (e := (simplicialHomotopyVertexEdge
    (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (Simplex.vertex X))).toTruncated) (f := e.toTruncated) he).mpr hInv
/-- 同じ実 augmentation の全単体族が与える、分解圏上の空間値全関手の比較同型。 -/
def dgModuleAugmentationUnderlyingSpaceIso :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationSourceLift R C PUnit.{1} F)) ≫
          dgHomUnderlyingSpaceInfinity R C)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgModuleAugmentationTargetLift R C PUnit.{1} F)) ≫
          dgHomUnderlyingSpaceInfinity R C) :=
  functorIsoOfPointwiseInvertibleHomotopy (dgModuleAugmentationUnderlyingSpaceHomotopy R C F) (by
    rintro ⟨s⟩
    obtain ⟨X, rfl⟩ := (Simplex.vertexEquiv (A := R)
      (D := DGModuleFunctorResolutionObject R C PUnit.{1} F)).symm.surjective s
    exact dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_isInvertible R C F X)
end SerrePositivity.InfinityCategories
