module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornFiniteRefinement
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramEdgeRefinement
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramHornSource

/-! # 実図式辺有限族の一つの追加実閉分母後の同時辺錐

概要：指定有限族の全辺に、一つの追加閉分母と同じ元の始対象から実充填・実分母辺錐を供給。
方針：全回収始域の厳密な共通対象を使い、有限残差原始元を同時に回収して実充填へ渡す。
規約：新 apex と頂点脚の辺間一致は別工程。使われ方：実有限図式の共通錐の組み立て。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f)

/-- 一つの追加実閉分母を使った、指定辺有限族の同時実充填データ。 -/
structure DGVerdierFiniteEdgeRefinement {m : ℕ} (e : Fin m → K _⦋1⦌) where
  q : D
  s : ForgetEnrichment.of (Complex A) q ⟶ C.denominator.obj.left
  denominator : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P
  refinements (i : Fin m) : DGVerdierDiagramEdgeRefinement A D C (e i)
  source_eq (i : Fin m) : (refinements i).q = q
  denominator_edge_eq (i : Fin m) :
    (dgClosedEdge A D (refinements i).s).edge = (dgClosedEdge A D s).edge

/-- 指定実図式辺の有限族には、一つの共通追加閉分母後の全実充填が同時に存在する。 -/
theorem dgVerdierFiniteEdgeRefinement_nonempty [IsDGPretriangulated A D]
    {m : ℕ} (e : Fin m → K _⦋1⦌) : Nonempty (DGVerdierFiniteEdgeRefinement A D C e) := by
  obtain ⟨T⟩ := dgLastHornFiniteRefinement_nonempty P
    (ForgetEnrichment.to (Complex A) C.denominator.obj.left)
    (fun i => dgVerdierDiagramEdgeHorn A D C (e i))
    (fun i => dgVerdierDiagramHorn_source A D C (e i))
    (fun i => dgVerdierDiagramLastClosed_mem A D P x C (e i))
  exact ⟨{
    q := T.q
    s := T.s
    denominator := T.denominator
    refinements := fun i => {
      q := (T.residuals i).q
      s := (T.residuals i).s
      denominator := (T.residuals i).denominator
      filler := (T.residuals i).solution.extension
      fac := (T.residuals i).solution.fac }
    source_eq := T.source_eq
    denominator_edge_eq := T.denominator_edge_eq }⟩

end SerrePositivity.InfinityCategories
