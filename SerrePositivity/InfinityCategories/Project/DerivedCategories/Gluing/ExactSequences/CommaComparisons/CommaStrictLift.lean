module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaBoundaryLift

/-! 厳密可換な augmentation 正方形を、第三 cochain が零の閉 comma 射に持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) Y.source)
  (b : ForgetEnrichment.of (Complex R) X.replacement ⟶
    ForgetEnrichment.of (Complex R) Y.replacement)
  (h : b ≫ Y.augmentation = X.augmentation ≫ F.onClosed.map a)

include h in
/-- 厳密可換性から、第三 cochain 零の境界式を得る。 -/
lemma dgGluingCommaStrictLift_boundary :
    δ (-1) 0 (0 : Cochain (𝟙_ (Complex R))
      (homObject R E X.replacement (F.obj Y.source)) (-1)) +
    Cochain.ofHom (biprod.lift (ForgetEnrichment.homTo (Complex R) a)
      (ForgetEnrichment.homTo (Complex R) b) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) = 0 := by
  rw [δ_zero, zero_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedDifference]
  have he := congrArg (fun k => ForgetEnrichment.homTo (Complex R) k) h
  rw [he, sub_self, Cochain.ofHom_zero]

/-- 同じ実二成分と第三 cochain 零を持つ閉 comma 射。 -/
def dgGluingCommaStrictLift : ForgetEnrichment.of (Complex R) X ⟶
    ForgetEnrichment.of (Complex R) Y :=
  ForgetEnrichment.homOf (Complex R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F X Y (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R) a) (ForgetEnrichment.homTo (Complex R) b) 0
      (dgGluingCommaStrictLift_boundary R C E F X Y a b h))

/-- 入力成分は、指定した同じ閉射。 -/
lemma dgGluingCommaStrictLift_source : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F).onClosed.map
    (dgGluingCommaStrictLift R C E F X Y a b h) = a := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) (dgGluingCommaStrictLift R C E F X Y a b h) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y) = a
  rw [dgGluingCommaStrictLift, ForgetEnrichment.homTo_homOf,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source, ForgetEnrichment.homOf_homTo]

/-- 比較対象の成分も、指定した同じ閉射。 -/
lemma dgGluingCommaStrictLift_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F).onClosed.map
      (dgGluingCommaStrictLift R C E F X Y a b h) = b := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) (dgGluingCommaStrictLift R C E F X Y a b h) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y) = b
  rw [dgGluingCommaStrictLift, ForgetEnrichment.homTo_homOf,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement, ForgetEnrichment.homOf_homTo]

/-- 第三 cochain は、全パラメータの比較として厳密に零。 -/
lemma dgGluingCommaStrictLift_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X Y (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R) (dgGluingCommaStrictLift R C E F X Y a b h)) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgGluingCommaStrictLift, ForgetEnrichment.homTo_homOf,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
