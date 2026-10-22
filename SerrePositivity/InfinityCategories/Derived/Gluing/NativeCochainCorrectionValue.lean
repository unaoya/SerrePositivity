module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainCorrectionValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismCorrectionValue

/-! 元 Hom の負 primitive に対する明示 cochain 補正は、元 augmentation の同じ実補正値となる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

lemma dgGluingNativePrismCorrectionValue_eq_cochain
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    dgGluingNativePrismCorrectionValue R C D M s β J k hk =
      dgGluingComplexCochainCorrectionValue.{u, max u v w} R (DGGluingObject R C D M)
        (-dgGluingHomPrimitive R C D M X Y) s β J k hk := by
  simp only [dgGluingNativePrismCorrectionValue, dgGluingComplexCochainCorrectionValue,
    Cochain.neg_v, ModuleCat.hom_neg, LinearMap.neg_apply, neg_neg]
  rfl

end SerrePositivity.InfinityCategories
