module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDegenerateTriangleCones

/-! # 退化二単体の二つの表示と標準三単体の一致

概要：同じ退化図式二単体の任意の基本退化表示は、同じ標準実三単体を与える。
方針：異なる退化番号の重なりは同じ二重退化頂点へ帰着し、単位条件と σσ 恒等式を使う。
規約：表示を選ぶことによる曖昧さを残さない。使われ方：二次充填の退化正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)

variable (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 二つの異なる基本退化表示が重なると、その標準三単体も厳密に一致する。 -/
lemma dgVerdierDegenerateTriangleCone_overlap
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge)
    (e e' : K _⦋1⦌)
    (he : K.σ 0 e = K.σ 1 e') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 0 e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 1 e' := by
  have hl : e = K.σ 0 (K.δ 0 e') :=
    (K.δ_comp_σ_self_apply (0 : Fin 2) e).symm.trans
      ((congrArg (K.δ (0 : Fin 3)) he).trans
        (K.δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) e'))
  have hr : e' = K.σ 0 (K.δ 1 e) :=
    (K.δ_comp_σ_succ_apply (1 : Fin 2) e').symm.trans
      ((congrArg (K.δ (2 : Fin 3)) he).symm.trans
        (K.δ_comp_σ_of_gt_apply (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) e))
  have hs : K.δ 1 e = K.δ 0 e' :=
    (congrArg (K.δ (1 : Fin 2)) hl).trans
      (K.δ_comp_σ_succ_apply (0 : Fin 1) (K.δ 0 e'))
  have hr' : e' = K.σ 0 (K.δ 0 e') := hr.trans (congrArg (K.σ (0 : Fin 1)) hs)
  have hL : (H e).simplex = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg (K.δ 0 e')).edge :=
    (congrArg (fun w => (H w).simplex) hl).trans (hunit (K.δ 0 e'))
  have hR : (H e').simplex = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg (K.δ 0 e')).edge :=
    (congrArg (fun w => (H w).simplex) hr').trans (hunit (K.δ 0 e'))
  exact (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ (1 : Fin 3)) hL).trans
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ_comp_σ_apply (i := (1 : Fin 2)) (j := (1 : Fin 2))
      le_rfl (C.leg (K.δ 0 e')).edge).trans
        (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ (2 : Fin 3)) hR).symm)

/-- 同じ退化図式二単体の任意の基本退化表示は、同じ標準実三単体を与える。 -/
lemma dgVerdierDegenerateTriangleCone_congr
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge)
    (i j : Fin 2) (e e' : K _⦋1⦌)
    (he : K.σ i e = K.σ j e') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H i e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H j e' := by
  fin_cases i <;> fin_cases j
  · have h : e = e' := (K.δ_comp_σ_self_apply (0 : Fin 2) e).symm.trans
      ((congrArg (K.δ (0 : Fin 3)) he).trans (K.δ_comp_σ_self_apply (0 : Fin 2) e'))
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 0) h
  · exact dgVerdierDegenerateTriangleCone_overlap A D C H hunit e e' he
  · exact (dgVerdierDegenerateTriangleCone_overlap A D C H hunit e' e he.symm).symm
  · have h : e = e' := (K.δ_comp_σ_self_apply (1 : Fin 2) e).symm.trans
      ((congrArg (K.δ (1 : Fin 3)) he).trans (K.δ_comp_σ_self_apply (1 : Fin 2) e'))
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 1) h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
