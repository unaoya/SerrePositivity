module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathPullback
public import SerrePositivity.InfinityCategories.Derived.ComplexQuasiIsoSpan
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComplex

/-! 同じ path 複体の実収縮・次数別全射性と、gluing Hom の元の差への適用。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded

def dgGluingCoconePathContraction {R : Type u} [CommRing R] (Q : Complex R) :
    Homotopy (𝟙 (mappingCocone (𝟙 Q))) 0 := identityCoconeContraction Q

lemma dgGluingCoconePathProjection_surjective {R : Type u} [CommRing R]
    (Q : Complex R) (n : ℤ) : Function.Surjective ((mappingCocone.fst (𝟙 Q)).f n) := by
  intro y
  refine ⟨(mappingCocone.inl (𝟙 Q)).v n n (add_zero n) y, ?_⟩
  exact ConcreteCategory.congr_hom (mappingCocone.inl_v_fst_f (𝟙 Q) n) y

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomComplex_path_isPullback (X Y : DGGluingObject R C D M) :
    IsPullback (dgGluingCoconePathMap (dgGluingDifference R C D M X Y))
      (mappingCocone.fst (dgGluingDifference R C D M X Y))
      (mappingCocone.fst (𝟙 (M.value X.left Y.right)))
      (dgGluingDifference R C D M X Y) :=
  dgGluingCoconePath_isPullback _

end SerrePositivity.InfinityCategories
