module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionFaces
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathProductPrimitiveZero
public import SerrePositivity.KST.LocalizingInvariants.CochainAlgebraProductNaturality

/-!
概要：connection の比較 cochain は、source 対角と恒等に関する積の比較を満たす。
方針：両評価と二重 primitive による一意性で二項の積を照合する。
規約：元の経路代数の乗法を使う。使われ方：connection の実代数射化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

/-- source 対角と恒等を両端に持つ積の比較 cochain。 -/
def connectionProductCochain :
    Cochain ((algebra R B).X ⊗ (algebra R B).X) (algebra R B).X (-1) :=
  ((tensorRightHom (algebra R B).X (algebra R B).X (algebra R B).X).f (-1)
    (connectionCochain R B)).comp
      (Cochain.ofHom ((𝟙 (algebra R B).X ⊗ₘ
        ((source R B).hom ≫ diagonalHom R B)) ≫ μ[(algebra R B).X])) (add_zero (-1)) +
  ((tensorLeftHom (algebra R B).X (algebra R B).X (algebra R B).X).f (-1)
    (connectionCochain R B)).comp
      (Cochain.ofHom ((𝟙 (algebra R B).X ⊗ₘ 𝟙 (algebra R B).X) ≫
        μ[(algebra R B).X])) (add_zero (-1))

lemma connectionCochain_mul : (Cochain.ofHom μ[(algebra R B).X]).comp
    (connectionCochain R B) (zero_add (-1)) = connectionProductCochain R B := by
  apply cochain_ext R B
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_source,
      Cochain.comp_zero]
    dsimp only [connectionProductCochain]
    rw [Cochain.add_comp, cochainRightProduct_post, cochainLeftProduct_post,
      connectionCochain_source, map_zero, map_zero, Cochain.zero_comp, Cochain.zero_comp,
      zero_add]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_target,
      mul_primitive]
    dsimp only [connectionProductCochain]
    rw [Cochain.add_comp, cochainRightProduct_post, cochainLeftProduct_post,
      connectionCochain_target, Category.assoc, diagonalHom_target,
      Category.comp_id, Category.id_comp]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_primitive,
      Cochain.comp_zero]
    dsimp only [connectionProductCochain]
    rw [Cochain.add_comp, rightProduct_primitive_zero R B _ _
      (connectionCochain_primitive R B) (by
        rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          diagonalHom_primitive, Cochain.comp_zero]),
      leftProduct_primitive_zero R B _ _ (connectionCochain_source R B)
        (connectionCochain_primitive R B), zero_add]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
