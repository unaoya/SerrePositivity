module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientPathPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientPathPullbackEquivalence

/-! 元の gluing Hom 空間から通常の係数 path 引き戻しへの実比較は同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomCoefficientPathPullbackComparison_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientPathPullbackComparison R C D M X Y =
      (dgGluingHomTwoEndpointProduct_isPullback R C D M X Y).isoPullback.hom ≫
        dgGluingCoefficientPathPullbackMap (M.value X.left Y.right)
          (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
            complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) := by
  apply pullback.hom_ext
  · simp only [dgGluingHomCoefficientPathPullbackComparison_path,
      dgGluingCoefficientPathPullbackMap, Category.assoc, pullback.map,
      pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
    rfl
  · simp only [dgGluingHomCoefficientPathPullbackComparison_inputs,
      dgGluingCoefficientPathPullbackMap, Category.assoc, pullback.map,
      pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]

lemma dgGluingHomCoefficientPathPullbackComparison_equivalence
    (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomCoefficientPathPullbackComparison R C D M X Y) := by
  let : KanComplex
      (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left) ⊗
        complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right)) :=
    F2.kanComplex_tensor _ _
  rw [dgGluingHomCoefficientPathPullbackComparison_factor]
  apply (dgGluingHomotopyEquivalence_precomp_iso_iff _ _).mpr
  exact dgGluingCoefficientPathPullbackMap_equivalence _ _

end SerrePositivity.InfinityCategories
