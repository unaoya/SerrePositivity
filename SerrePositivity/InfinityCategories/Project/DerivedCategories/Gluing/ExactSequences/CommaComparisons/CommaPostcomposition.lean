module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ClosedCompositionCochain
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaProjections
/-! 実 comma の閉射による後合成の第三 cochain を二項に分ける。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

def dgGluingCommaPostInsertion : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z :=
  (ρ_ _).inv ≫ _ ◁ ForgetEnrichment.homTo (Complex R) f

def dgGluingCommaPostImageArrow : ForgetEnrichment.of (Complex R) (F.obj Y.source) ⟶
    ForgetEnrichment.of (Complex R) (F.obj Z.source) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F).comp F).onClosed.map f

lemma dgGluingCommaPostImageArrow_map :
    ForgetEnrichment.homTo (Complex R) f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z =
      ForgetEnrichment.homTo (Complex R) (dgGluingCommaPostImageArrow R C E F Y Z f) := rfl

lemma dgGluingCommaPost_first : (Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Z) (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).comp
      (Cochain.ofHom (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement)
        (dgGluingCommaPostImageArrow R C E F Y Z f)))
      (add_zero (-1)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochain_rightClosed E X.replacement (F.obj Y.source) (F.obj Z.source)
    (dgGluingCommaPostImageArrow R C E F Y Z f) (ForgetEnrichment.homTo (Complex R) f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z) (dgGluingCommaPostImageArrow_map R C E F Y Z f)
    (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)

lemma dgGluingCommaPost_second : (Cochain.ofHom (dgGluingCommaPostInsertion R C E F X Y Z f)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z) (zero_add (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)).comp
      ((Cochain.ofHom ((ρ_ (homObject R E X.replacement Y.replacement)).inv ≫
        (homObject R E X.replacement Y.replacement) ◁ ForgetEnrichment.homTo (Complex R) f)).comp
        (((tensorLeftHom (homObject R E X.replacement Y.replacement)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
          (homObject R E Y.replacement (F.obj Z.source))).f (-1)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z)).comp
          (Cochain.ofHom (eComp (Complex R) X.replacement Y.replacement (F.obj Z.source)))
          (add_zero (-1))) (zero_add (-1))) (zero_add (-1)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochain_second_factor E X.replacement Y.replacement (F.obj Z.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)
    (ForgetEnrichment.homTo (Complex R) f) (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
