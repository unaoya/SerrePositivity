module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.GradedPostcomposition

/-! 全次数の後合成と、標準円錐代表射のような閉零射による後合成との整合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (x y z w : E)
  (a : ForgetEnrichment.of (Complex R) z ⟶ ForgetEnrichment.of (Complex R) w)

/-- 係数 Hom への閉後合成は、全次数の後合成を作用後の閉後合成へ移す。 -/
lemma dgGluingGradedPostcomposition_postcompose_map :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) y) a ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E x y w =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E x y z ≫
      homPostcompose (homObject R E x y)
        (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) a) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition
  rw [← curryRight_naturality_source, ← curryRight_naturality_target]
  congr 1
  rw [tensorHom_id, Category.assoc]
  erw [BraidedCategory.braiding_naturality_left_assoc]
  erw [eComp_eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y) a]
  rfl

/-- 同じ等式を、指定整数次数の元に作用させた cochain として回収する。 -/
lemma dgGluingGradedPostcomposition_postcompose {p : ℤ} (g : GradedHom R y z p) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E x y z).f p g).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) x) a)) (add_zero p) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E x y w).f p
      ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) y) a).f p g) := by
  have he := congrArg (fun b => b.f p g)
    (dgGluingGradedPostcomposition_postcompose_map R E x y z w a)
  exact he.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
