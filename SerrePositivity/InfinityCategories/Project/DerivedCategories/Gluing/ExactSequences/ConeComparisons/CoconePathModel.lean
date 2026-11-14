module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconePathPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexQuasiIsoSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomComplex

/-! 同じ path 複体の実収縮・次数別全射性と、gluing Hom の元の差への適用。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded

def dgGluingCoconePathContraction {R : Type u} [CommRing R] (Q : Complex R) :
    Homotopy (𝟙 (mappingCocone (𝟙 Q))) 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.identityCoconeContraction Q

lemma dgGluingCoconePathProjection_surjective {R : Type u} [CommRing R]
    (Q : Complex R) (n : ℤ) : Function.Surjective ((mappingCocone.fst (𝟙 Q)).f n) := by
  intro y
  refine ⟨(mappingCocone.inl (𝟙 Q)).v n n (add_zero n) y, ?_⟩
  exact ConcreteCategory.congr_hom (mappingCocone.inl_v_fst_f (𝟙 Q) n) y

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomComplex_path_isPullback (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y))
      (mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y))
      (mappingCocone.fst (𝟙 (M.value X.left Y.right)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePath_isPullback _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
