module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierIdentityEdgeCones

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)


/-- 図式辺の等式に沿って、その同じ三辺を持つ辺錐を型付き輸送する。 -/
def dgVerdierEdgeConeTransport {e e' : K _⦋1⦌} (he : e = e')
    (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 e'))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e').map ((truncation 2).map f)) (C.leg (K.δ 0 e')) := he ▸ H

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 図式辺の等式による輸送は、辺錐の元の実二単体を保つ。 -/
lemma dgVerdierEdgeConeTransport_simplex {e e' : K _⦋1⦌} (he : e = e')
    (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))) :
    (dgVerdierEdgeConeTransport A D C he H).simplex = H.simplex := by
  cases he
  rfl

variable (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 退化辺では標準終点退化、それ以外では元の辺錐を選ぶ全辺族。 -/
def dgVerdierDiagramNormalizeEdgeCone (e : K _⦋1⦌) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) := by
  classical
  exact if he : e = K.σ 0 (K.δ 1 e) then
    dgVerdierEdgeConeTransport A D C he.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramIdentityEdgeCone A D C (K.δ 1 e))
  else H e

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 正規化した退化辺錐の台は、その元の頂点脚の標準終点退化。 -/
lemma dgVerdierDiagramNormalizeEdgeCone_identity_simplex (v : K _⦋0⦌) :
    (dgVerdierDiagramNormalizeEdgeCone A D C H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge := by
  classical
  have hv : K.δ 1 (K.σ 0 v) = v := K.δ_comp_σ_succ_apply (0 : Fin 1) v
  have he : K.σ 0 v = K.σ 0 (K.δ 1 (K.σ 0 v)) := congrArg (K.σ (0 : Fin 1)) hv.symm
  unfold dgVerdierDiagramNormalizeEdgeCone
  rw [dite_eq_left he, dgVerdierEdgeConeTransport_simplex]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramIdentityEdgeCone_simplex A D C _).trans
    (congrArg (fun w => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg w).edge) hv)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 正規化した退化辺錐全体は、同じ頂点脚の標準辺錐と一致する。 -/
lemma dgVerdierDiagramNormalizeEdgeCone_identity (v : K _⦋0⦌) :
    dgVerdierDiagramNormalizeEdgeCone A D C H (K.σ 0 v) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramIdentityEdgeCone A D C v := by
  apply Truncated.Edge.CompStruct.ext
  exact dgVerdierDiagramNormalizeEdgeCone_identity_simplex A D C H v

variable {C} (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C)

/-- 正規化した全辺錐の同じ閉細分でも、全退化辺錐は新頂点脚の標準退化のまま。 -/
lemma DGVerdierClosedVertexRefinement.normalizedIdentityEdgeCone_simplex (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCompStruct A D R (K.σ 0 v)
      (dgVerdierDiagramNormalizeEdgeCone A D C H (K.σ 0 v))).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge := by
  rw [dgVerdierDiagramNormalizeEdgeCone_identity]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.identityEdgeCone_simplex A D R v

end SerrePositivity.InfinityCategories.Project.DerivedCategories
