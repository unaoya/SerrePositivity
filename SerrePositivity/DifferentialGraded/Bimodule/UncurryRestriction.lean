module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryHom

/-! # uncurryHomを因子へ制限した際の計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 第一因子に制限したuncurryHomは元の右作用。 -/
lemma uncurryHom_first (M : Bimodule A B C) (c : C) (x y : Bᵒᵖ) :
    dgTensorFirstHom A Bᵒᵖ C c x y ≫ M.uncurryHom (x, c) (y, c) =
      (M.rightAt c).map x y := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  have h := M.uncurryHom_apply (x := (x, c)) (y := (y, c)) f
    (unitElement A c).val (add_zero p)
  rw [leftCochain_unit] at h
  simp only [mul_zero, Int.negOnePow_zero, one_smul, Cochain.comp_id] at h
  exact (congrArg (fun t => (M.uncurryHom (x, c) (y, c)).f p t)
    (dgTensorFirstHom_apply A Bᵒᵖ C c x y p f)).trans h

/-- 第二因子に制限したuncurryHomは元の左作用。 -/
lemma uncurryHom_second (M : Bimodule A B C) (b : B) (c d : C) :
    dgTensorSecondHom A Bᵒᵖ C (op b) c d ≫ M.uncurryHom (op b, c) (op b, d) =
      (M.leftAt b).map c d := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  have h := M.uncurryHom_apply (x := (op b, c)) (y := (op b, d))
    (unitElement A (op b)).val g (zero_add q)
  have hr := DGFunctor.map_unitElement A (M.rightAt c).toFunctor (op b)
  rw [complex_unitElement] at hr
  have he := congrArg (fun f : Cochain (M.value b c) (M.value b c) 0 =>
    f.comp (M.leftCochain g b) (zero_add q)) hr
  simp only [Cochain.id_comp] at he
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  exact (congrArg (fun t => (M.uncurryHom (op b, c) (op b, d)).f q t)
    (dgTensorSecondHom_apply A Bᵒᵖ C (op b) c d q g)).trans (h.trans he)

end SerrePositivity.DifferentialGraded.Bimodule
