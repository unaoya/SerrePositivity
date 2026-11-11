module
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison
public import SerrePositivity.KST.Fibration.WeakStringVertexPostcomposition
public import SerrePositivity.KST.Fibration.KernelPostcomposition

/-! # 元の初期頂点と全核値 cofiber の有限積の後合成写像 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の有限比較の値域の、元の初期成分と全核値 cofiber 成分による後合成。 -/
def weakStringFinitePostMap {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    ((multiRealizationFunctor r).obj (closedStableModel
      (ClosedStablePredicate.top (sInputModel A))) ⊗
      ∏ᶜ fun _ : Fin n => (multiRealizationFunctor r).obj
        (closedStableModel (kernelClosedPredicate (f ≫ q : A ⟶ C)))) ⟶
    ((multiRealizationFunctor r).obj (closedStableModel
      (ClosedStablePredicate.top (sInputModel B))) ⊗
      ∏ᶜ fun _ : Fin n => (multiRealizationFunctor r).obj
        (closedStableModel (kernelClosedPredicate q))) :=
  (multiRealizationFunctor r).map (topPostExact f) ⊗ₘ
    Limits.Pi.map (fun _ : Fin n => (multiRealizationFunctor r).map (kernelPostExact f q))

/-- 後合成の有限積写像の初期成分は、元の全頂点部分圏の後合成を回収する。 -/
lemma weakStringFinitePostMap_initial {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    weakStringFinitePostMap f q n r ≫ fst _ _ =
      fst _ _ ≫ (multiRealizationFunctor r).map (topPostExact f) := tensorHom_fst _ _

/-- 後合成の有限積写像の各 cofiber 成分は、元の核への後合成を回収する。 -/
lemma weakStringFinitePostMap_cofiber {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin n) :
    weakStringFinitePostMap f q n r ≫ snd _ _ ≫ Pi.π _ i =
      snd _ _ ≫ Pi.π _ i ≫ (multiRealizationFunctor r).map (kernelPostExact f q) := by
  simp only [weakStringFinitePostMap, tensorHom_snd_assoc, Limits.Pi.map_π]

end SerrePositivity.KST.Fibration
