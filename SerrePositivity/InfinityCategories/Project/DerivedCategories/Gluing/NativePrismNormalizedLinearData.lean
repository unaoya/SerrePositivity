module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativePinchedPrismNormalizedCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexIsoEvaluation

/-! 元 prism の実正規化係数を同じ複体模型の全線形データへ束ね、明示族の全データと照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativePrismNormalizedLinearData (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v w} (M.value X.left Y.right)) R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) n :=
  fun i => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).hom.f i.val.2
    ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).hom.f i.val.2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedCoefficient R C D M s β i.val.1 i.val.2 i.property.1
        i.property.2))

lemma dgGluingNativePrismNormalizedLinearData_eq (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    dgGluingNativePrismNormalizedLinearData R C D M s (SSet.stdSimplex.objEquiv β).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
        (Opposite.op ⦋n⦌) (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s)) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
    (Opposite.op ⦋n⦌) (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component
    J k hJ hk
  have hc := congrArg
    (fun a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.representable R X.left) (M.rightAt Y.right) k =>
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).hom.f k
        ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).hom.f k a))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedCoefficient_comparison R C D M s β J k hJ hk)
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexIso_inv_hom_apply (dgYonedaIso R X.left (M.rightAt Y.right)) k
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).inv.f k z)
  have hη := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexIso_inv_hom_apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)) k z
  exact hc.trans ((congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).hom.f k a)
    hy).trans hη)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
