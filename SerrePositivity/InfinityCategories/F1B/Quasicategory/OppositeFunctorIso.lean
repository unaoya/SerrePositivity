module

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.OppositeFunctorHom

/-!
概要：反転した関手の同型から元の関手の同型を、指定 Hom 全単射の逆で復元する。
方針：順射と逆射を両方戻し、反転の単射性で逆恒等式を確認する。
規約：指定した二胞体の類を保つ。使われ方：K-8 の余単位の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F1B
namespace SerrePositivity.KST.LocalizingInvariants

variable {A D : SSet.{u}} [Quasicategory D] {F G : A ⟶ D}

def restoredFunctorIso (e : FunctorIso (SSet.opFunctor.map G) (SSet.opFunctor.map F)) :
    FunctorIso F G where
  hom := (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F G).symm e.hom
  inv := (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv G F).symm e.inv
  hom_inv_id := by
    apply (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F).injective
    rw [SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp, oppositeFunctorHom_id]
    simp only [Equiv.apply_symm_apply]
    exact e.inv_hom_id
  inv_hom_id := by
    apply (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv G G).injective
    rw [SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp, oppositeFunctorHom_id]
    simp only [Equiv.apply_symm_apply]
    exact e.hom_inv_id

end SerrePositivity.KST.LocalizingInvariants
