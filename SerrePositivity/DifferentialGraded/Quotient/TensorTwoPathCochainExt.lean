module
public import SerrePositivity.DifferentialGraded.Quotient.TensorPathCochainExt
public import SerrePositivity.DifferentialGraded.Quotient.TensorRightPathCochainExt

/-! # 二つの全path直和のtensorからの任意次数cochainの判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorTwoPathCochain_ext (S : Set D) (x y z : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (internalHom A D S x y ⊗ internalHom A D S y z) T p)
    (h : ∀ w v : Word S, (Cochain.ofHom (ι A D S x y w ⊗ₘ ι A D S y z v)).comp f
      (zero_add p) = (Cochain.ofHom (ι A D S x y w ⊗ₘ ι A D S y z v)).comp g (zero_add p)) :
    f = g := by
  apply tensorRightPathCochain_ext A D S x y (internalHom A D S y z) p
  intro w
  apply tensorLeftPathCochain_ext A D S y z (term A D w x y) p
  intro v
  simpa only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    ← tensorHom_def'] using h w v

end SerrePositivity.DifferentialGraded.DGQuotient
