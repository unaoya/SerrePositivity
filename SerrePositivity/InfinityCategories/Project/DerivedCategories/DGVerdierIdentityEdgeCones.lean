module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedEdgeCones
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDegenerateLegRefinement

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)

/-- 退化図式辺には、元の頂点脚の終点を繰り返す標準辺錐を選ぶ。 -/
def dgVerdierDiagramIdentityEdgeCone (v : K _⦋0⦌) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 (K.σ 0 v)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.σ 0 v)).map ((truncation 2).map f))
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

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 恒等図式辺の標準辺錐の台は、元の同じ頂点脚の標準終点退化。 -/
lemma dgVerdierDiagramIdentityEdgeCone_simplex (v : K _⦋0⦌) :
    (dgVerdierDiagramIdentityEdgeCone A D C v).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge := rfl

variable {C} (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C)

/-- 恒等図式辺の標準辺錐の閉細分は、新しい同じ頂点脚の標準終点退化。 -/
lemma DGVerdierClosedVertexRefinement.identityEdgeCone_simplex (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCompStruct A D R (K.σ 0 v)
      (dgVerdierDiagramIdentityEdgeCone A D C v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.refine_degenerateLeg A D R v

end SerrePositivity.InfinityCategories.Project.DerivedCategories
