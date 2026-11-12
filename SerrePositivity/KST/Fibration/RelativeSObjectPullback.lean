module
public import SerrePositivity.KST.Fibration.RelativeSObjectBridge
public import SerrePositivity.KST.Fibration.WeakStringConstantPullback

/-! # 元の object 比較を保つ相対 S の核四角形のホモトピー引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の object S 比較と core S の射の自然性。 -/
lemma objectCoreSExactMap_naturality {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    objectSConstructionFunctor.map (sInputExactMap f) ≫ objectToCoreSRealization B.obj =
      objectToCoreSRealization A.obj ≫ simplicialDiagonalFunctor.map (coreSExactMap f) :=
  objectCoreRealizationComparison.naturality (sInputExactMap f)

/-- object 比較を前合成しても、元の相対 S の核四角形は厳密に可換。 -/
theorem relativeSObjectKernelSquare {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    CommSq
      (objectToCoreSRealization A.obj ≫ simplicialDiagonalFunctor.map
        (relativeSimplicialSConstructionCoreInclusion (f.hom ≫ q.hom)))
      (objectSConstructionFunctor.map (sInputExactMap f))
      (simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom))
      (objectToCoreSRealization B.obj ≫ simplicialDiagonalFunctor.map
        (relativeSimplicialSConstructionCoreInclusion q.hom)) := by
  constructor
  rw [Category.assoc, ← Functor.map_comp, (relativeSimplicialKernelSquare f q.hom).w,
    Functor.map_comp, ← Category.assoc, ← objectCoreSExactMap_naturality, Category.assoc]

/-- 元の相対 S の object 四角形は、定数 W 列の同じ四角形との厳密比較で homotopy pullback。 -/
theorem relativeSObjectKernelSquare_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : IsHomotopyPullback (relativeSObjectKernelSquare i q) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (relativeSObjectKernelSquare i q) (weakStringConstantPostSquare i q 1)
    (objectSingleRealizationComparison (sInputModel A))
    (relativeSWeakStringMultiComparison (i ≫ q : A ⟶ C))
    (objectSingleRealizationComparison (sInputModel B))
    (relativeSWeakStringMultiComparison q) ?_ ?_ ?_ ?_
    (objectSingleRealizationComparison_localized_isIso _)
    (relativeSWeakStringMultiComparison_localized_isIso _)
    (objectSingleRealizationComparison_localized_isIso _)
    (relativeSWeakStringMultiComparison_localized_isIso _)).mpr
  · exact weakStringConstantPostSquare_homotopyPullback h 0
  · exact (Category.assoc _ _ _).trans
      (relativeSWeakStringMultiComparison_coreInclusion_object (i ≫ q : A ⟶ C))
  · exact objectSingleRealizationComparison_naturality (sInputExactMap i)
  · exact relativeSWeakStringMultiComparison_postcomp i q
  · exact (Category.assoc _ _ _).trans
      (relativeSWeakStringMultiComparison_coreInclusion_object q)

end SerrePositivity.KST.Fibration
