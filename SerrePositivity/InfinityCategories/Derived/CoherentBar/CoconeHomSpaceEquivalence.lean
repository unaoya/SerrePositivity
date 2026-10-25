module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceIso
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.DGNerve.PinchedKan
/-!
概要：正規化実 bar の全 Hom 比較は、実際の単体的ホモトピー同値である。
方針：構成済みの厳密な単体集合同型を Kan 複体間のホモトピー同値として使う。
規約：公開 MC を代入した無条件版を併設し、native 余極限性とは区別する。
使われ方：native 余錐の標準 Hom の族との接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (dgCoherentBarCoconeHomSpaceComparison R D F hMC y) := by
  have h : IsQCatEquivalence (dgCoherentBarCoconeHomSpaceComparison R D F hMC y) :=
    (qCatEquivalenceOfIso (dgCoherentBarCoconeHomSpaceIso R D F hMC y)).isQCatEquivalence
  exact h.isSimplicialHomotopyEquivalence

lemma dgCoherentBarCoconeHomSpaceComparisonUnconditional_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence
      (dgCoherentBarCoconeHomSpaceComparisonUnconditional R D F y) :=
  dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence R D F
    (dgCoherentBarTheta_maurerCartan R D F) y

end SerrePositivity.InfinityCategories
