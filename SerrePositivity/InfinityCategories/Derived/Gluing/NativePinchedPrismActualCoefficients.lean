module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismCorrectionSum
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismActualCoefficients

/-! 元の nerve 比較で実際に使う augmentation prism の混合係数を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

lemma dgGluingNativePinchedPrismActual_mixed (β : Fin (n + 2) →o Fin 2)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    HEq ((dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        (s.val.map (dgGluingToComma R C D M)) β).hom I a b k hI ha hb hk)
      (dgGluingCommaPrismMainCoefficient R D (RightModule R C) M.toFunctor
          (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData I a b k hI ha hb hk +
        dgGluingCommaPrismCorrectionSum R D (RightModule R C) M.toFunctor
          (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData
          β I a b k hI ha hb hk) := by
  have he := congrArg (fun t => dgCommaAugmentationPrismSimplex R D (RightModule R C)
    M.toFunctor t β) (dgGluingNativeCommaPinchedSimplex_val R C D M s).symm
  exact (Simplex.hom_heq_of_eq he I a b k hI ha hb hk).trans
    (dgGluingCommaPrismActual_mixed R D (RightModule R C) M.toFunctor
      (dgGluingNativeCommaPinchedSimplex R C D M s).val β I a b k hI ha hb hk hpa hpb)

end SerrePositivity.InfinityCategories
