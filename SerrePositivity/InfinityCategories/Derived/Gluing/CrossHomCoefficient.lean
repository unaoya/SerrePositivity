module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeBottomInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomZeroComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorSubcategories

/-! 二充満因子の逆向き全 Hom は、同じ双加群係数 M[-1] と標準包含で擬同型。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X : DGGluingCFactor R C D M) (Y : DGGluingDFactor R C D M)

/-- 比較元を保持したまま、係数の −1 シフトを実 Hom の bottom 成分へ含める。 -/
def dgGluingCrossHomCoefficientMap :
    (M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧ ⟶
      homObject R (DGGluingObject R C D M) X.val Y.val :=
  dgGluingCoconeBottomInclusion (dgGluingDifference R C D M X.val Y.val)

/-- 両対角 Hom のホモトピー零性により、同じ実係数包含は擬同型。 -/
lemma dgGluingCrossHomCoefficientMap_quasiIso :
    QuasiIso (dgGluingCrossHomCoefficientMap R C D M X Y) := by
  apply dgGluingCoconeBottomInclusion_quasiIso
  exact dgGluingComplexBiproduct_homotopyZero R _ _
    (dgGluingFactorIsZero_hom_target R C X.val.left Y.val.left Y.property)
    (dgGluingFactorIsZero_hom_source R D X.val.right Y.val.right X.property)

end SerrePositivity.InfinityCategories
