module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorPathCochainExt
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorRightPathCochainExt

/-! # 二つの全path直和のtensorからの任意次数cochainの判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma tensorTwoPathCochain_ext (x y z : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y ⊗ C.internalHom A D I y z) T p)
    (h : ∀ w v : List I,
      (Cochain.ofHom (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z)).comp f
      (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z)).comp g (zero_add p)) :
    f = g := by
  apply C.tensorRightPathCochain_ext A D I x y (C.internalHom A D I y z) p
  intro w
  apply C.tensorLeftPathCochain_ext A D I y z (C.term A D I w x y) p
  intro v
  simpa only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    ← tensorHom_def'] using h w v

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
