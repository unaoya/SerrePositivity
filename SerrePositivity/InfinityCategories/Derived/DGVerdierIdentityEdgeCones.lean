module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierClosedEdgeCones
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDegenerateLegRefinement

/-! # 恒等図式辺の標準辺錐と閉細分による保存

概要：退化図式辺の辺錐を頂点脚の終点退化から指定し、同じ閉細分がこの選択を保つ。
方針：合成単位の標準二単体と図式の退化自然性から実辺錐を作り、固定脚の退化保存を適用。
規約：実単体の厳密一致。使われ方：全辺錐の恒等整合的選択。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f)

/-- 退化図式辺には、元の頂点脚の終点を繰り返す標準辺錐を選ぶ。 -/
def dgVerdierDiagramIdentityEdgeCone (v : K _⦋0⦌) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 (K.σ 0 v)))
      ((edgeOfSimplex (K.σ 0 v)).map ((truncation 2).map f))
      (C.leg (K.δ 0 (K.σ 0 v))) where
  simplex := (Truncated.Edge.CompStruct.compId (C.leg v)).simplex
  d₂ := by
    have he : K.δ 1 (K.σ 0 v) = v := K.δ_comp_σ_succ_apply (0 : Fin 1) v
    exact (Truncated.Edge.CompStruct.compId (C.leg v)).d₂.trans
      (congrArg (fun w => (C.leg w).edge) he.symm)
  d₁ := by
    have he : K.δ 0 (K.σ 0 v) = v := K.δ_comp_σ_self_apply (0 : Fin 1) v
    exact (Truncated.Edge.CompStruct.compId (C.leg v)).d₁.trans
      (congrArg (fun w => (C.leg w).edge) he.symm)
  d₀ := by
    have hn := ConcreteCategory.congr_hom (f.naturality (SimplexCategory.σ (0 : Fin 1)).op) v
    exact (Truncated.Edge.CompStruct.compId (C.leg v)).d₀.trans hn.symm

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 恒等図式辺の標準辺錐の台は、元の同じ頂点脚の標準終点退化。 -/
lemma dgVerdierDiagramIdentityEdgeCone_simplex (v : K _⦋0⦌) :
    (dgVerdierDiagramIdentityEdgeCone A D C v).simplex =
      (dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge := rfl

variable {C} (R : DGVerdierClosedVertexRefinement A D C)

/-- 恒等図式辺の標準辺錐の閉細分は、新しい同じ頂点脚の標準終点退化。 -/
lemma DGVerdierClosedVertexRefinement.identityEdgeCone_simplex (v : K _⦋0⦌) :
    (DGVerdierClosedVertexRefinement.edgeCompStruct A D R (K.σ 0 v)
      (dgVerdierDiagramIdentityEdgeCone A D C v)).simplex =
      (dgVerdierOver A D P x : SSet).σ 1
        ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge :=
  DGVerdierClosedVertexRefinement.refine_degenerateLeg A D R v

end SerrePositivity.InfinityCategories
