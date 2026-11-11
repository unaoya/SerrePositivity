module
public import SerrePositivity.KST.Fibration.WeakStringObjectRelativePostcomp
public import SerrePositivity.KST.Fibration.WeakStringRelativeCoreRealization

/-! # 相対 S から W 列の core S 実現への実比較が元の包含側の写像を保つ -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の各 W 列の object/core 比較は、元の包含側の完全関手に関して自然。 -/
lemma weakStringObjectCoreComparison_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    Functor.whiskerRight (weakStringStablePostcomp f q) objectSConstructionFunctor ≫
      weakStringObjectCoreComparison q =
        weakStringObjectCoreComparison (f ≫ q : A ⟶ C) ≫
          Functor.whiskerRight (weakStringStablePostcomp f q) coreSRealizationFunctor := by
  apply NatTrans.ext
  funext n
  exact objectCoreRealizationComparison.naturality (weakStringPostExact f q n.unop)

/-- 元の相対 S の対角からの実比較射は、元の包含側の完全関手に関して厳密に自然。 -/
theorem relativeSWeakStringCoreComparison_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom) ≫
      relativeSWeakStringCoreComparison q =
        relativeSWeakStringCoreComparison (f ≫ q : A ⟶ C) ≫
          simplicialDiagonalFunctor.map
            (Functor.whiskerRight (weakStringStablePostcomp f q) coreSRealizationFunctor) := by
  have h := weakStringObjectRelativeDiagonalIso_postcomp f q
  have hi : simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom) ≫
      (weakStringObjectRelativeDiagonalIso q).inv =
        (weakStringObjectRelativeDiagonalIso (f ≫ q : A ⟶ C)).inv ≫
          simplicialDiagonalFunctor.map
            (Functor.whiskerRight (weakStringStablePostcomp f q) objectSConstructionFunctor) := by
    apply (cancel_epi (weakStringObjectRelativeDiagonalIso (f ≫ q : A ⟶ C)).hom).1
    rw [← Category.assoc, ← h, Category.assoc]
    simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hc := congrArg simplicialDiagonalFunctor.map (weakStringObjectCoreComparison_postcomp f q)
  rw [Functor.map_comp, Functor.map_comp] at hc
  unfold relativeSWeakStringCoreComparison
  rw [← Category.assoc, hi, Category.assoc, hc, ← Category.assoc]

/-- 元の相対 S の核側の写像を、同じ W 列の core S 実現の写像へ運ぶ可換四角形。 -/
theorem relativeSWeakStringCoreComparison_square {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    CommSq (relativeSWeakStringCoreComparison (f ≫ q : A ⟶ C))
      (simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom))
      (simplicialDiagonalFunctor.map
        (Functor.whiskerRight (weakStringStablePostcomp f q) coreSRealizationFunctor))
      (relativeSWeakStringCoreComparison q) :=
  ⟨(relativeSWeakStringCoreComparison_postcomp f q).symm⟩

end SerrePositivity.KST.Fibration
