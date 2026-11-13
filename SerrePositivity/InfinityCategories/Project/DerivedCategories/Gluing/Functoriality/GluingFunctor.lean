module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.CrossHom.CrossHomCoefficientTransformation

/-! 半直交順序 ⟨D,C⟩ の逆向き Hom を与える、元の双加群の gluing dg 関手。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 双加群の共変 dg 関手を、逆向き Hom の規約に合わせて −1 シフトする。 -/
def dgGluingFunctor : DGFunctor R D (RightModule R C) :=
  M.toFunctor.comp (moduleShiftDG R C (-1))

lemma dgGluingFunctor_value (c : C) (d : D) :
    ((dgGluingFunctor R C D M).obj d).obj (op c) =
      (M.value c d)⟦(-1 : ℤ)⟧ := rfl

lemma dgGluingFunctor_factor_value [Small.{u} D]
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).obj Y).obj (op X) =
      ((dgGluingFunctor R C D M).obj Y.val.right).obj (op X.val.left) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
