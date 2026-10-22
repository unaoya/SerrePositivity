module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismCorrectionSum

/-! 元 prism の混合切断和は、削除符号を除くと主係数円柱の同じ負 primitive に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial

lemma dgGluingPinchedPrismCorrectionSign {n : ℕ}
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    (((withLast J).filter ((second J hJ).castSucc < ·)).card : ℤ).negOnePow =
      -(((J.filter (J.min' (Index.nonempty hJ) < ·)).card : ℤ) + 1).negOnePow := by
  rw [card_above_withLast]
  exact sign_second J hJ

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

lemma dgGluingNativePinchedPrismCorrectionSum_cylinder
    (β : Fin (n + 2) →o Fin 2) (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) (hβ : β (second J hJ).castSucc = 1) :
    HEq (dgGluingCommaPrismCorrectionSum R D (RightModule R C) M.toFunctor
        (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData β (withLast J)
        (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
        (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
        (max_withLast J _) (by rw [card_withLast]; omega))
      ((((J.filter (J.min' (Index.nonempty hJ) < ·)).card : ℤ) + 1).negOnePow •
        (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (k + 1 - 1)
          (((dgGluingCochainCylinderPrimitive (dgGluingHomComplex R C D M X Y)).comp
            (Cochain.ofHom (dgGluingHomCoefficientCylinderExtension R C D M X Y))
            (add_zero (-1))).v (k + 1) (k + 1 - 1) (by omega)
            ((toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
              (LinearData.erase_nonempty hJ _ (J.min'_mem _))
              (by
                have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ))
                omega)))) := by
  refine (dgGluingNativePinchedPrismCorrectionSum_primitive R C D M s β J hJ k hk hβ).trans ?_
  apply heq_of_eq
  rw [dgGluingHomCoefficientCylinderExtension_primitive, Cochain.neg_v]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]
  rw [dgGluingPinchedPrismCorrectionSign J hJ]
  simp only [Units.neg_smul, smul_neg]

end SerrePositivity.InfinityCategories
