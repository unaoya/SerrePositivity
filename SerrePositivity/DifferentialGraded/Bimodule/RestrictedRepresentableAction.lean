module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestriction
public import SerrePositivity.DifferentialGraded.Category.TensorComposition
public import SerrePositivity.DifferentialGraded.Module.RestrictionAction

/-! # 積dg圏の代表加群を右Bへ制限したときの斉次作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

omit [Small.{u} B] [Small.{u} C] in
lemma tensorRightRestrictionInclusion_map (c : C) (x y : Bᵒᵖ) :
    (tensorRightRestrictionInclusion A B C c).map x y = dgTensorFirstHom A Bᵒᵖ C c x y := by
  change dgTensorFirstHom A Bᵒᵖ C c x y ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [Small.{u} B] [Small.{u} C] in
lemma restrictedRepresentable_action (b₀ : B) (c₀ c : C) {x y : Bᵒᵖ}
    {p r s k n : ℤ} (hk : r + s = k) (hn : k + p = n)
    (f : GradedHom A x y p) (h : GradedHom A x.unop b₀ r) (g : GradedHom A c₀ c s) :
    moduleAction A
      (restrictModule A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (tensorRightRestrictionInclusion A B C c)
        (representable A (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C)))) f
      (ιTensorObj (x.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) r s k hk (h ⊗ₜ[A] g)) hn =
    ιTensorObj (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (r + p) s n (by omega)
      (forward A (x := y.unop) (y := x.unop) (z := b₀) f h (by omega) ⊗ₜ[A] g) := by
  rw [restrictModule_action, tensorRightRestrictionInclusion_map, representable_action]
  rw [opposite_forward]
  change (p * k).negOnePow • forward A (D := DGTensorCategory A Bᵒᵖ C)
    (x := ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))
    (y := ((x, c) : DGTensorCategory A Bᵒᵖ C))
    (z := ((y, c) : DGTensorCategory A Bᵒᵖ C))
    (dgTensorElement A h g hk) ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f) hn = _
  rw [dgTensorFirstHom_apply A Bᵒᵖ C c x y p f]
  rw [dgTensor_forward_of_sum A
    (x := ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))
    (y := ((x, c) : DGTensorCategory A Bᵒᵖ C))
    (z := ((y, c) : DGTensorCategory A Bᵒᵖ C))
    h g f (unitElement A c).val hk (add_zero p) rfl (add_zero s) hn]
  change (p * k).negOnePow • ((s * p).negOnePow •
    ιTensorObj (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (r + p) s n (by omega)
      (forward A (D := Bᵒᵖ) (x := op b₀) (y := x) (z := y) h f rfl ⊗ₜ[A]
        forward A (D := C) g (unitElement A c).val (add_zero s))) = _
  rw [unit_forward A g]
  rw [opposite_forward A B (op b₀) x y r p (r + p) rfl h f]
  change (p * k).negOnePow • ((s * p).negOnePow •
    ιTensorObj (y.unop ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (r + p) s n (by omega)
      (((r * p).negOnePow • forward A (D := B) (x := y.unop) (y := x.unop)
        (z := b₀) (p := p) (q := r) (n := r + p) f h (by omega)) ⊗ₜ[A] g)) = _
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul, smul_smul]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  have he : p * k + (s * p + r * p) = 2 * (p * k) := by rw [← hk]; ring
  rw [he, Int.negOnePow_two_mul, Units.val_one, one_smul]

end SerrePositivity.DifferentialGraded
