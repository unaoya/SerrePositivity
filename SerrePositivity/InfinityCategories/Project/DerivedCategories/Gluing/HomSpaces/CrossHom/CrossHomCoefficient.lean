module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconeBottomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.CrossHom.CrossHomZeroComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FactorSubcategories

/-! 二充満因子の逆向き全 Hom は、同じ双加群係数 M[-1] と標準包含で擬同型。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M)

/-- 比較元を保持したまま、係数の −1 シフトを実 Hom の bottom 成分へ含める。 -/
def dgGluingCrossHomCoefficientMap :
    (M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧ ⟶
      homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X.val Y.val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X.val Y.val)

/-- 両対角 Hom のホモトピー零性により、同じ実係数包含は擬同型。 -/
lemma dgGluingCrossHomCoefficientMap_quasiIso :
    QuasiIso (dgGluingCrossHomCoefficientMap R C D M X Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_quasiIso
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexBiproduct_homotopyZero R _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_hom_target R C X.val.left Y.val.left Y.property)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_hom_source R D X.val.right Y.val.right X.property)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
