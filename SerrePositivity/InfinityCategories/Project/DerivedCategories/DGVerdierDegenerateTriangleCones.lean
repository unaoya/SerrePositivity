module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteUnitalTwoCones

/-! # 退化図式二単体の標準実三単体と全四面

概要：単位整合的な全辺錐の下で、退化二単体の標準充填を辺錐の正番号退化として固定。
方針：面退化恒等式、元の辺錐の三面、図式の退化自然性、単位条件を照合する。
規約：全四面を厳密に保つ。使われ方：二次充填の退化整合的な正規化。
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

/-- 実三単体が、指定図式二単体と同じ全辺錐を四面に持つ条件。 -/
def DGVerdierTriangleConeBoundary (σ : K _⦋2⦌) (U : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌) : Prop :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 U = f.app _ σ ∧
    ∀ i : Fin 3, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ U = (H (K.δ i σ)).simplex

/-- 退化図式二単体 σi e の標準三単体は、指定辺錐の σ(i+1)。 -/
def dgVerdierDegenerateTriangleCone (i : Fin 2) (e : K _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ i.succ (H e).simplex

/-- 標準退化三単体の零面は、その元の退化図式二単体。 -/
lemma dgVerdierDegenerateTriangleCone_face0 (i : Fin 2) (e : K _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (dgVerdierDegenerateTriangleCone A D C H i e) =
      f.app _ (K.σ i e) := by
  have hd := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_of_le_apply
    (i := (0 : Fin 3)) (j := i) (Fin.zero_le _) (H e).simplex
  have hn := ConcreteCategory.congr_hom (f.naturality (SimplexCategory.σ i).op) e
  exact hd.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ i) (H e).d₀).trans hn.symm)

/-- 標準退化三単体の各錐面は、その元の図式境界辺の同じ指定辺錐。 -/
lemma dgVerdierDegenerateTriangleCone_face_cone
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge)
    (i : Fin 2) (e : K _⦋1⦌) (j : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ j.succ (dgVerdierDegenerateTriangleCone A D C H i e) =
      (H (K.δ j (K.σ i e))).simplex := by
  fin_cases i <;> fin_cases j
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_self_apply (1 : Fin 3) (H e).simplex).trans
      (congrArg (fun w => (H w).simplex) (K.δ_comp_σ_self_apply (0 : Fin 2) e)).symm
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_succ_apply (1 : Fin 3) (H e).simplex).trans
      (congrArg (fun w => (H w).simplex) (K.δ_comp_σ_succ_apply (0 : Fin 2) e)).symm
  · have hd := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_of_gt_apply
      (i := (2 : Fin 3)) (j := (1 : Fin 2))
      (by decide) (H e).simplex
    have hk := K.δ_comp_σ_of_gt_apply (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) e
    exact hd.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ (1 : Fin 2)) (H e).d₂).trans
      ((hunit (K.δ 1 e)).symm.trans (congrArg (fun w => (H w).simplex) hk).symm))
  · have hd := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_of_le_apply
      (i := (1 : Fin 3)) (j := (1 : Fin 2))
      (by decide) (H e).simplex
    have hk := K.δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) e
    exact hd.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ (1 : Fin 2)) (H e).d₁).trans
      ((hunit (K.δ 0 e)).symm.trans (congrArg (fun w => (H w).simplex) hk).symm))
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_self_apply (2 : Fin 3) (H e).simplex).trans
      (congrArg (fun w => (H w).simplex) (K.δ_comp_σ_self_apply (1 : Fin 2) e)).symm
  · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ_comp_σ_succ_apply (2 : Fin 3) (H e).simplex).trans
      (congrArg (fun w => (H w).simplex) (K.δ_comp_σ_succ_apply (1 : Fin 2) e)).symm

/-- 単位条件付き全辺錐の下で、全退化二単体の標準三単体は同じ全四面を持つ。 -/
lemma dgVerdierDegenerateTriangleCone_boundary
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge)
    (i : Fin 2) (e : K _⦋1⦌) :
    DGVerdierTriangleConeBoundary A D C H (K.σ i e)
      (dgVerdierDegenerateTriangleCone A D C H i e) :=
  ⟨dgVerdierDegenerateTriangleCone_face0 A D C H i e,
    dgVerdierDegenerateTriangleCone_face_cone A D C H hunit i e⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
