module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.CrossHom.CrossHomFunctors
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Projections

/-! 二つの実係数 dg 関手の全 Hom 写像を、同じ評価と shift 作用で記述する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M

lemma dgGluingCrossHomFunctor_map_π
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).map Y Z ≫ moduleHomπ R A _ _ X =
      yonedaHom R G Y.val Z.val ≫
        moduleHomπ R G (representable R Y.val) (representable R Z.val) X.val := by
  change ((𝟙 _ ≫ yonedaHom R G Y.val Z.val) ≫
    moduleRestrictionHom R A G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorInclusion R C D M).op _ _) ≫
    moduleHomπ R A
      (restrictModule R A G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorInclusion R C D M).op (representable R Y.val))
      (restrictModule R A G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorInclusion R C D M).op (representable R Z.val)) X = _
  rw [Category.assoc, moduleRestrictionHom_π, Category.id_comp]
  rfl

lemma dgGluingCrossCoefficientFunctor_map_π
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).map Y Z ≫ moduleHomπ R A _ _ X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y.val Z.val ≫
        M.toFunctor.map Y.val.right Z.val.right ≫
        moduleHomπ R C (M.rightAt Y.val.right) (M.rightAt Z.val.right) X.val.left ≫
        shiftHom (-1) (M.value X.val.left Y.val.right) (M.value X.val.left Z.val.right) := by
  change ((((𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).map Y.val Z.val) ≫
    M.toFunctor.map Y.val.right Z.val.right) ≫
    moduleRestrictionHom R A C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).op _ _) ≫
    moduleShiftHom R A (-1) _ _) ≫ moduleHomπ R A
      (shiftModule (-1) (restrictModule R A C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).op
        (M.rightAt Y.val.right)))
      (shiftModule (-1) (restrictModule R A C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).op
        (M.rightAt Z.val.right))) X = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map, Category.id_comp]
  simp only [Category.assoc, moduleShiftHom_π, moduleRestrictionHom_π_assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
