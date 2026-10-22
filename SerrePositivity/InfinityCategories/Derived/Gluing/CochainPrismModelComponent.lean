module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainPrismComponentFormula

/-! 元 dg Hom 上で制限した明示全 prism の実出力を、同じ二端点・一切断の係数式で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex DGNerve DGNerve.PinchedHom
open MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  {a b : C} (x y : E) (f g : homObject R C a b ⟶ homObject R E x y)
  (h : Cochain (homObject R C a b) (homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f)) {n : ℕ}
  (s : (DGNerve.pinchedHom R C a b) _⦋n⦌)

lemma dgGluingCochainPrism_model_component (β : (Δ[1] : SSet.{max u v}) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (toLinearData ((dgGluingCochainAugmentationPrism R E x y (homObject R C a b) f g h he).app
        (Opposite.op ⦋n⦌) (β, (pinchedComplexModelIso a b).hom.app (Opposite.op ⦋n⦌) s))).component
      J k hJ hk =
      if (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 1 then
        g.f k ((toLinearData s).component J k hJ hk)
      else f.f k ((toLinearData s).component J k hJ hk) +
        dgGluingCochainPrismCorrectionValue R C E x y h s (SSet.stdSimplex.objEquiv β).toOrderHom
          J k hk := by
  let z : ((Δ[1] : SSet.{max u v}) ⊗ DGNerve.pinchedHom R C a b).obj
      (Opposite.op ⦋n⦌) := (β, s)
  have ht := ConcreteCategory.congr_hom (C := Type (max u v))
    (X := ((Δ[1] : SSet.{max u v}) ⊗ DGNerve.pinchedHom R C a b).obj (Opposite.op ⦋n⦌))
    (Y := (DGNerve.pinchedHom R E x y).obj (Opposite.op ⦋n⦌))
    (NatTrans.congr_app (dgGluingCochainAugmentationPrism_model_input
      R C E a b x y f g h he) (Opposite.op ⦋n⦌)) z
  change (dgGluingCochainAugmentationPrism R E x y (homObject R C a b) f g h he).app
      (Opposite.op ⦋n⦌) (β, (pinchedComplexModelIso a b).hom.app (Opposite.op ⦋n⦌) s) =
    dgGluingIdentityCommaPinchedPrismSimplex R E
      (pinchedHomChainMapSimplex (dgGluingCochainIdentityCommaLift
        R E x y (homObject R C a b) f g h he) s) (SSet.stdSimplex.objEquiv β).toOrderHom at ht
  rw [ht]
  exact dgGluingCochainPrism_component_formula R C E x y f g h he s _ J k hJ hk

end SerrePositivity.InfinityCategories
