module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPostBottom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeExtraction
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-! 実 comma 後合成の cocone の二成分と、回収した下辺を元の二射影・像の後合成へ同定。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

/-- source と replacement の実後合成を、同じ順の直和にする鎖写像。 -/
def dgGluingCommaPostComponents :
    (homObject R C X.source Y.source ⊞ homObject R E X.replacement Y.replacement) ⟶
      (homObject R C X.source Z.source ⊞ homObject R E X.replacement Z.replacement) :=
  biprod.map
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F).onClosed.map f))
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F).onClosed.map f))

/-- 閉 comma 射の実後合成は、同じ二射影の直和と第一 cocone 射影を保つ。 -/
lemma dgGluingCommaPost_fst :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f ≫
      mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Z) =
    mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) ≫
      dgGluingCommaPostComponents R C E F X Y Z f := by
  apply biprod.hom_ext
  · have he := dgHomMap_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F)
      (ForgetEnrichment.of (Complex R) X) f
    simp only [dgGluingCommaPostComponents, Category.assoc, biprod.map_fst]
    exact he
  · have he := dgHomMap_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F)
      (ForgetEnrichment.of (Complex R) X) f
    simp only [dgGluingCommaPostComponents, Category.assoc, biprod.map_snd]
    exact he

/-- 回収した cocone の下辺は、同じ像の閉射による実 Hom 後合成。 -/
lemma dgGluingCommaPost_extractBottom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Z) (dgGluingCommaPostComponents R C E F X Y Z f)
      (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)
      (dgGluingCommaPost_fst R C E F X Y Z f) =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R C E F Y Z f) := by
  apply Cochain.ofHom_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom_cochain]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_bottom R C E F X Y Z f

/-- 同じ像の閉射は、元の source 閉射を F で送った閉射と一致。 -/
lemma dgGluingCommaPostImageArrow_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R C E F Y Z f =
      F.onClosed.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F).onClosed.map f) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow, EnrichedFunctor.forget_map,
    EnrichedFunctor.comp_map, ForgetEnrichment.homTo_homOf, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
