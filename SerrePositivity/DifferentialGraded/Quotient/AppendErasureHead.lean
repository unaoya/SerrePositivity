module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureTensorTransport
public import SerrePositivity.DifferentialGraded.Quotient.AppendRightPrepend
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaces

/-! # 全右pathへの連結と先頭ε消去の整合式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 後方pathを連結してから先頭εを消す項は、先に先頭εを消した連結と一致する。 -/
lemma appendRight_eraseFirst {S : Set D} (b : S) (w : Word S) (x y z : D) :
    ((Cochain.ofHom
      ((α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (internalHom A D S y z)).hom ≫
       (homObject A D x b.val) ◁
         (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
       (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ appendRight A D w b.val y z))).comp
      (eraseMiddle A (homObject A D x b.val) (internalHom A D S b.val z)) (zero_add 1)).comp
      (Cochain.ofHom (internalPrepend A D S x b.val z)) (add_zero 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y) (term A D w x y)).f 1
      (eraseFirst A D b w x y)).comp (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) := by
  rw [eraseMiddle_tensorRight_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, Category.assoc,
    ← appendRight_prepend, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
