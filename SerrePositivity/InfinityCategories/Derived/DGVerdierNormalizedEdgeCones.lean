module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierIdentityEdgeCones

/-! # 全辺錐の恒等整合的な正規化と閉細分での保存

概要：任意の全辺錐の選択を、退化辺では頂点脚の標準終点退化を選ぶ族へ直す。
方針：辺の等式に沿う型付き輸送は台を保ち、標準退化の閉細分保存を適用する。
規約：二次以上の退化の正規化は別工程。使われ方：有限二次図式の恒等整合性。
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


/-- 図式辺の等式に沿って、その同じ三辺を持つ辺錐を型付き輸送する。 -/
def dgVerdierEdgeConeTransport {e e' : K _⦋1⦌} (he : e = e')
    (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 e'))
      ((edgeOfSimplex e').map ((truncation 2).map f)) (C.leg (K.δ 0 e')) := he ▸ H

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 図式辺の等式による輸送は、辺錐の元の実二単体を保つ。 -/
lemma dgVerdierEdgeConeTransport_simplex {e e' : K _⦋1⦌} (he : e = e')
    (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))) :
    (dgVerdierEdgeConeTransport A D C he H).simplex = H.simplex := by
  cases he
  rfl

variable (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 退化辺では標準終点退化、それ以外では元の辺錐を選ぶ全辺族。 -/
def dgVerdierDiagramNormalizeEdgeCone (e : K _⦋1⦌) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) := by
  classical
  exact if he : e = K.σ 0 (K.δ 1 e) then
    dgVerdierEdgeConeTransport A D C he.symm (dgVerdierDiagramIdentityEdgeCone A D C (K.δ 1 e))
  else H e

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 正規化した退化辺錐の台は、その元の頂点脚の標準終点退化。 -/
lemma dgVerdierDiagramNormalizeEdgeCone_identity_simplex (v : K _⦋0⦌) :
    (dgVerdierDiagramNormalizeEdgeCone A D C H (K.σ 0 v)).simplex =
      (dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge := by
  classical
  have hv : K.δ 1 (K.σ 0 v) = v := K.δ_comp_σ_succ_apply (0 : Fin 1) v
  have he : K.σ 0 v = K.σ 0 (K.δ 1 (K.σ 0 v)) := congrArg (K.σ (0 : Fin 1)) hv.symm
  unfold dgVerdierDiagramNormalizeEdgeCone
  rw [dite_eq_left he, dgVerdierEdgeConeTransport_simplex]
  exact (dgVerdierDiagramIdentityEdgeCone_simplex A D C _).trans
    (congrArg (fun w => (dgVerdierOver A D P x : SSet).σ 1 (C.leg w).edge) hv)

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 正規化した退化辺錐全体は、同じ頂点脚の標準辺錐と一致する。 -/
lemma dgVerdierDiagramNormalizeEdgeCone_identity (v : K _⦋0⦌) :
    dgVerdierDiagramNormalizeEdgeCone A D C H (K.σ 0 v) =
      dgVerdierDiagramIdentityEdgeCone A D C v := by
  apply Truncated.Edge.CompStruct.ext
  exact dgVerdierDiagramNormalizeEdgeCone_identity_simplex A D C H v

variable {C} (R : DGVerdierClosedVertexRefinement A D C)

/-- 正規化した全辺錐の同じ閉細分でも、全退化辺錐は新頂点脚の標準退化のまま。 -/
lemma DGVerdierClosedVertexRefinement.normalizedIdentityEdgeCone_simplex (v : K _⦋0⦌) :
    (DGVerdierClosedVertexRefinement.edgeCompStruct A D R (K.σ 0 v)
      (dgVerdierDiagramNormalizeEdgeCone A D C H (K.σ 0 v))).simplex =
      (dgVerdierOver A D P x : SSet).σ 1
        ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge := by
  rw [dgVerdierDiagramNormalizeEdgeCone_identity]
  exact DGVerdierClosedVertexRefinement.identityEdgeCone_simplex A D R v

end SerrePositivity.InfinityCategories
