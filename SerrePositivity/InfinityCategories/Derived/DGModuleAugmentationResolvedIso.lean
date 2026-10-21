module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInvertsQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationUnlifted
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationProjectiveIso
/-!
概要：元の全 augmentation ホモトピーを半自由出力分解へ送り、全関手比較同型を得る。
方針：元の実頂点辺と準同型反転を使い、入力前合成比較へ接続する。
規約：augmentation の終点の射影性・入力の Small 性を仮定しない。
使われ方：一般 kernel の導来合成の実関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open DGNerve.HomotopyComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 同じ実 augmentation を、指定の半自由出力分解へ送る全単体ホモトピー。 -/
def dgModuleAugmentationResolvedHomotopy :
    SSet.Homotopy
      (dgNerve.map (dgModuleAugmentationSource R C E F) ≫
        dgModuleResolvedInfinity R (RightModule R E) K H)
      (dgNerve.map (dgModuleAugmentationTarget R C E F) ≫
        dgModuleResolvedInfinity R (RightModule R E) K H) :=
  functorHomotopyPostcomp (dgModuleAugmentationUnliftedHomotopy R C E F)
    (dgModuleResolvedInfinity R (RightModule R E) K H)
/-- augmentation の指定出力が準同型なら、同じ実頂点辺は可逆。 -/
lemma dgModuleAugmentationResolvedHomotopy_vertex_isInvertible
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation))
    (X : DGModuleFunctorResolutionObject R C E F) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge
      (dgModuleAugmentationResolvedHomotopy R C E K F H) (Simplex.vertex X)).toTruncated := by
  have hi := dgModuleResolvedInfinity_invertsQuasiIso R (RightModule R E) K H
    (dgClosedEdge R (RightModule R E) X.augmentation)
    (by simpa only [dgClosedEdge_closed] using hq X)
  apply (isInvertibleEdge_congr (e := (simplicialHomotopyVertexEdge
    (dgModuleAugmentationResolvedHomotopy R C E K F H) (Simplex.vertex X)).toTruncated)
    (f := (dgClosedEdge R (RightModule R E) X.augmentation).map
      ((truncation 2).map (dgModuleResolvedInfinity R (RightModule R E) K H))) ?_).mpr hi
  change (dgModuleResolvedInfinity R (RightModule R E) K H).app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge
      (dgModuleAugmentationUnliftedHomotopy R C E F) (Simplex.vertex X)).edge = _
  rw [dgModuleAugmentationUnliftedHomotopy_vertex_edge]
  rfl
/-- 同じ augmentation の全単体ホモトピーが与える全関手比較同型。 -/
def dgModuleAugmentationResolvedIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgNerve.map (dgModuleAugmentationSource R C E F) ≫
        dgModuleResolvedInfinity R (RightModule R E) K H)
      (dgNerve.map (dgModuleAugmentationTarget R C E F) ≫
        dgModuleResolvedInfinity R (RightModule R E) K H) :=
  functorIsoOfPointwiseInvertibleHomotopy
    (dgModuleAugmentationResolvedHomotopy R C E K F H) (by
      intro x
      obtain ⟨X, rfl⟩ := (Simplex.vertexEquiv
        (A := R) (D := DGModuleFunctorResolutionObject R C E F)).symm.surjective x
      exact dgModuleAugmentationResolvedHomotopy_vertex_isInvertible R C E K F H hq X)
/-- 元の二つの dg 関手の半自由出力分解を、同じ augmentation で比較する。 -/
def dgModuleAugmentationResolvedComparisonIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgModuleResolvedInfinity R (DGModuleFunctorResolutionObject R C E F) K
        ((dgModuleAugmentationSource R C E F).comp H))
      (dgModuleResolvedInfinity R (DGModuleFunctorResolutionObject R C E F) K
        ((dgModuleAugmentationTarget R C E F).comp H)) :=
  dgModuleResolvedInfinity_precompIso R _ (RightModule R E) K
    (dgModuleAugmentationSource R C E F) H ≪≫
    dgModuleAugmentationResolvedIso R C E K F H hq ≪≫
    (dgModuleResolvedInfinity_precompIso R _ (RightModule R E) K
      (dgModuleAugmentationTarget R C E F) H).symm
end SerrePositivity.InfinityCategories
