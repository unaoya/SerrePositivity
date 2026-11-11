module
public import SerrePositivity.KST.Fibration.WeakStringCofiberPostcomparison
public import SerrePositivity.KST.Fibration.WeakStringCofiberRealization
public import SerrePositivity.KST.SConstruction.MultiRealizationFunctorIso

/-! # 元の全合成辺の核値 cofiber の後合成と全正有限反復実現 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の共通 cofiber 射は、元の包含側の完全関手と核への後合成に全正反復で整合する。 -/
theorem weakStringCofiberMultiMap_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory}
    (α : ⦋1⦌ ⟶ n) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakStringPostExact f q n)) ≫
      AnodyneHomotopy.anodyneQ.map (weakStringCofiberMultiMap q α (r + 1)) =
        AnodyneHomotopy.anodyneQ.map
          (weakStringCofiberMultiMap (f ≫ q : A ⟶ C) α (r + 1)) ≫
          AnodyneHomotopy.anodyneQ.map
            ((multiRealizationFunctor (r + 1)).map (kernelPostExact f q)) := by
  have h := multiRealization_map_positive_localized_eq_of_functorIso r
    (weakStringKernelCofiber_postcomp f q α)
  simpa only [Functor.map_comp, weakStringCofiberMultiMap] using h

end SerrePositivity.KST.Fibration
