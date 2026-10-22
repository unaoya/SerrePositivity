module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismNormalizedCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexIsoEvaluation

/-! 元 prism の実正規化係数を同じ複体模型の全線形データへ束ね、明示族の全データと照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativePrismNormalizedLinearData (β : Fin (n + 1) →o Fin 2) :
    LinearData (D := DGComplexPinchedModel.{u, max u v w} (M.value X.left Y.right)) R
      (complexPinchedSource _) (complexPinchedTarget _) n :=
  fun i => (complexUnitHomIso (M.value X.left Y.right)).hom.f i.val.2
    ((dgYonedaIso R X.left (M.rightAt Y.right)).hom.f i.val.2
      (dgGluingNativePrismNormalizedCoefficient R C D M s β i.val.1 i.val.2 i.property.1
        i.property.2))

lemma dgGluingNativePrismNormalizedLinearData_eq (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    dgGluingNativePrismNormalizedLinearData R C D M s (SSet.stdSimplex.objEquiv β).toOrderHom =
      toLinearData ((dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
        (Opposite.op ⦋n⦌) (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s)) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  let z := (toLinearData ((dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
    (Opposite.op ⦋n⦌) (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component
    J k hJ hk
  have hc := congrArg
    (fun a : GradedHom R (representable R X.left) (M.rightAt Y.right) k =>
      (complexUnitHomIso (M.value X.left Y.right)).hom.f k
        ((dgYonedaIso R X.left (M.rightAt Y.right)).hom.f k a))
    (dgGluingNativePrismNormalizedCoefficient_comparison R C D M s β J k hJ hk)
  have hy := dgGluingComplexIso_inv_hom_apply (dgYonedaIso R X.left (M.rightAt Y.right)) k
    ((complexUnitHomIso (M.value X.left Y.right)).inv.f k z)
  have hη := dgGluingComplexIso_inv_hom_apply (complexUnitHomIso (M.value X.left Y.right)) k z
  exact hc.trans ((congrArg (fun a => (complexUnitHomIso (M.value X.left Y.right)).hom.f k a)
    hy).trans hη)

end SerrePositivity.InfinityCategories
