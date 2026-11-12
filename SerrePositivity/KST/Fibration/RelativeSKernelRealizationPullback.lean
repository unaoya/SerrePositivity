module
public import SerrePositivity.KST.Fibration.RelativeSObjectPullback

/-! # 元の core S 包含を保つ相対 S の核四角形の実現後のホモトピー引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の単体的な核四角形を、四つの対象と四辺を保って対角へ送る。 -/
theorem relativeSKernelRealizationSquare {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    CommSq
      (simplicialDiagonalFunctor.map
        (relativeSimplicialSConstructionCoreInclusion (f.hom ≫ q.hom)))
      (simplicialDiagonalFunctor.map (coreSExactMap f))
      (simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom))
      (simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q.hom)) :=
  simplicialDiagonalFunctor.map_commSq (relativeSimplicialKernelSquare f q.hom)

/-- 元の相対 S 核四角形そのものは、元の core 包含のまま実現後に homotopy pullback。 -/
theorem relativeSKernelRealizationSquare_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    IsHomotopyPullback (relativeSKernelRealizationSquare i q) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (relativeSObjectKernelSquare i q) (relativeSKernelRealizationSquare i q)
    (objectToCoreSRealization A.obj) (𝟙 _) (objectToCoreSRealization B.obj) (𝟙 _)
    ?_ ?_ ?_ ?_ (objectToCoreSRealization_localized_isIso A.obj) (by infer_instance)
    (objectToCoreSRealization_localized_isIso B.obj) (by infer_instance)).mp
  · exact relativeSObjectKernelSquare_homotopyPullback h
  · rw [Category.comp_id]
  · exact objectCoreSExactMap_naturality i
  · simp only [Category.comp_id, Category.id_comp]
  · rw [Category.comp_id]

end SerrePositivity.KST.Fibration
