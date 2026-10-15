module
public import SerrePositivity.DifferentialGraded.Tensor.ModuleParameter
public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-! # パラメータ付きbalanced族とtensor加群のbalanced族 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- associatorで族の表示を替えたときの二つのbalanced条件は同値。 -/
lemma parameter_balanced_condition_iff (K : Complex A) (M : RightModule A D)
    (N : LeftModule A D) {T : Complex A}
    (a : ∀ x, K ⊗ objectFamily A D M N x ⟶ T) (x y : D) :
    ((rightAction A D (tensorModule K M) x y ▷ N.obj x) ≫
        (α_ K (M.obj (op x)) (N.obj x)).hom ≫ a x =
      (α_ (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        (K ⊗ M.obj (op y)) ◁ leftAction A D N x y ≫
          (α_ K (M.obj (op y)) (N.obj y)).hom ≫ a y) ↔
    ((K ◁ (rightAction A D M x y ▷ N.obj x)) ≫ a x =
      (K ◁ ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y)) ≫ a y) := by
  rw [rightAction_tensorModule, comp_whiskerRight, Category.assoc,
    associator_naturality_middle_assoc, associator_naturality_right_assoc, ← pentagon_assoc]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [cancel_epi, cancel_epi]

/-- Kを左に置くbalanced族を、tensor加群のbalanced族へ移す。 -/
def paramTensorFamily {M : RightModule A D} {N : LeftModule A D} {K T : Complex A}
    (a : ParamFamily A D M N K T) : BalancedFamily A D (tensorModule K M) N T := by
  refine ⟨fun x => (α_ K (M.obj (op x)) (N.obj x)).hom ≫ a.val x, ?_⟩
  intro x y
  exact (parameter_balanced_condition_iff A D K M N a.val x y).2 (a.property x y)

/-- tensor加群のbalanced族を、Kを左に置く族へ戻す。 -/
def tensorParamFamily {M : RightModule A D} {N : LeftModule A D} {K T : Complex A}
    (b : BalancedFamily A D (tensorModule K M) N T) : ParamFamily A D M N K T := by
  refine ⟨fun x => (α_ K (M.obj (op x)) (N.obj x)).inv ≫ b.val x, ?_⟩
  intro x y
  apply (parameter_balanced_condition_iff A D K M N _ x y).1
  simpa only [Iso.hom_inv_id_assoc] using b.property x y

/-- パラメータ複体を右加群のtensorへ移す族の同値。 -/
def paramTensorFamilyEquiv (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) : ParamFamily A D M N K T ≃ BalancedFamily A D (tensorModule K M) N T where
  toFun := paramTensorFamily A D
  invFun := tensorParamFamily A D
  left_inv a := by
    apply Subtype.ext
    funext x
    exact Iso.inv_hom_id_assoc (α_ K (M.obj (op x)) (N.obj x)) (a.val x)
  right_inv b := by
    apply Subtype.ext
    funext x
    exact Iso.hom_inv_id_assoc (α_ K (M.obj (op x)) (N.obj x)) (b.val x)

end SerrePositivity.DifferentialGraded.BalancedTensor
