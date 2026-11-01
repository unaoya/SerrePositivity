module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-! 閉射による実 Hom の後合成。二射影と全次数の第三 cochain を保持する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

/-- 元の dg gluing 圏の閉射による、全 Hom 複体の実後合成。 -/
def dgGluingPostcomposition :
    dgGluingHomComplex R C D M X Y ⟶ dgGluingHomComplex R C D M X Z :=
  eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f

lemma dgGluingPostcomposition_left :
    dgGluingPostcomposition R C D M X Y Z f ≫ dgGluingLeftHomMap R C D M X Z =
      dgGluingLeftHomMap R C D M X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.left)
          ((dgGluingLeft R C D M).onClosed.map f) :=
  dgHomMap_postcompose (dgGluingLeft R C D M) _ f

lemma dgGluingPostcomposition_right :
    dgGluingPostcomposition R C D M X Y Z f ≫ dgGluingRightHomMap R C D M X Z =
      dgGluingRightHomMap R C D M X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.right)
          ((dgGluingRight R C D M).onClosed.map f) := by
  have h := dgHomMap_postcompose (dgGluingRight R C D M)
    (ForgetEnrichment.of (Complex R) X) f
  simpa only [dgGluingRight_map] using! h

/-- 比較差の始域における、左右の実後合成の直和。 -/
def dgGluingPostcompositionComponents :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ⟶
      (homObject R C X.left Z.left ⊞ homObject R D X.right Z.right) :=
  biprod.lift
    (biprod.fst ≫ eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.left)
      ((dgGluingLeft R C D M).onClosed.map f))
    (biprod.snd ≫ eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.right)
      ((dgGluingRight R C D M).onClosed.map f))

lemma dgGluingPostcomposition_fst :
    dgGluingPostcomposition R C D M X Y Z f ≫
        mappingCocone.fst (dgGluingDifference R C D M X Z) =
      mappingCocone.fst (dgGluingDifference R C D M X Y) ≫
        dgGluingPostcompositionComponents R C D M X Y Z f := by
  apply biprod.hom_ext
  · simpa only [dgGluingPostcompositionComponents, Category.assoc, biprod.lift_fst,
      dgGluingLeftHomMap] using dgGluingPostcomposition_left R C D M X Y Z f
  · simpa only [dgGluingPostcompositionComponents, Category.assoc, biprod.lift_snd,
      dgGluingRightHomMap] using dgGluingPostcomposition_right R C D M X Y Z f

/-- 閉射を全 Hom tensor の第二因子へ挿入する同じ実鎖写像。 -/
def dgGluingPostcompositionInsertion :
    dgGluingHomComplex R C D M X Y ⟶
      dgGluingHomComplex R C D M X Y ⊗ dgGluingHomComplex R C D M Y Z :=
  (ρ_ _).inv ≫ _ ◁ ForgetEnrichment.homTo (Complex R) f

lemma dgGluingPostcomposition_eq :
    dgGluingPostcomposition R C D M X Y Z f =
      dgGluingPostcompositionInsertion R C D M X Y Z f ≫
        dgGluingComposition R C D M X Y Z := rfl

/-- 閉射の挿入後にも、tensor の次数符号を含む第三 cochain をそのまま保持する。 -/
def dgGluingPostcompositionPrimitive :
    Cochain (dgGluingHomComplex R C D M X Y) (M.value X.left Z.right) (-1) :=
  (Cochain.ofHom (dgGluingPostcompositionInsertion R C D M X Y Z f)).comp
    (dgGluingCompositePrimitive R C D M X Y Z) (zero_add (-1))

lemma dgGluingPostcomposition_comparison :
    dgGluingHomComparison R C D M X Z _ (dgGluingPostcomposition R C D M X Y Z f) =
      dgGluingPostcompositionPrimitive R C D M X Y Z f := by
  rw [dgGluingPostcomposition_eq]
  change (Cochain.ofHom (_ ≫ _)).comp (dgGluingHomPrimitive R C D M X Z) _ = _
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  have hc := dgGluingComposition_comparison R C D M X Y Z
  change (Cochain.ofHom (dgGluingComposition R C D M X Y Z)).comp
    (dgGluingHomPrimitive R C D M X Z) _ = _ at hc
  rw [hc]
  rfl

end SerrePositivity.InfinityCategories
