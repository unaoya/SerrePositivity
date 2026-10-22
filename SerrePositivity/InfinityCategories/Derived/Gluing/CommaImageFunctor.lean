module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageCompositePrimitive
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections

/-! 任意関手の comma を、二射影・比較 cochain・全 dg 合成を保って標的恒等 comma へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
local notation "IX" => dgGluingCommaImageObject R C E F X
local notation "IY" => dgGluingCommaImageObject R C E F Y
local notation "IZ" => dgGluingCommaImageObject R C E F Z
local notation "aXY" => dgGluingCommaImageHomMap R C E F X Y
local notation "aYZ" => dgGluingCommaImageHomMap R C E F Y Z
local notation "aXZ" => dgGluingCommaImageHomMap R C E F X Z

omit Y Z in
lemma dgGluingCommaImageHomMap_identity :
    dgFunctorCommaIdentity R C E F X ≫ dgGluingCommaImageHomMap R C E F X X =
      dgFunctorCommaIdentity R E E (DGFunctor.id E) IX := by
  apply dgFunctorCommaHom_ext R E E (DGFunctor.id E) IX IX _
  · rw [Category.assoc, dgGluingCommaImageHomMap_source,
      dgFunctorCommaIdentity_image, dgFunctorCommaIdentity_source]
    rfl
  · rw [Category.assoc, dgGluingCommaImageHomMap_replacement,
      dgFunctorCommaIdentity_replacement, dgFunctorCommaIdentity_replacement]
    rfl
  · rw [dgGluingCommaImageHomComparison, dgFunctorCommaIdentity_comparison,
      dgFunctorCommaIdentity_comparison]

lemma dgGluingCommaImageHomMap_composition :
    dgFunctorCommaComposition R C E F X Y Z ≫ aXZ =
      (aXY ⊗ₘ aYZ) ≫ dgFunctorCommaComposition R E E (DGFunctor.id E) IX IY IZ := by
  apply dgFunctorCommaHom_ext R E E (DGFunctor.id E) IX IZ _
  · have hl : (dgFunctorCommaComposition R C E F X Y Z ≫ aXZ) ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IX IZ =
      dgFunctorCommaSourceComposite R C E F X Y Z ≫ F.map X.source Z.source := by
      rw [Category.assoc, dgGluingCommaImageHomMap_source, dgFunctorCommaImageHomMap,
        ← Category.assoc, dgFunctorCommaComposition_source]
    have hr : ((aXY ⊗ₘ aYZ) ≫ dgFunctorCommaComposition R E E (DGFunctor.id E) IX IY IZ) ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IX IZ =
      (dgFunctorCommaImageHomMap R C E F X Y ⊗ₘ dgFunctorCommaImageHomMap R C E F Y Z) ≫
        eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
      rw [Category.assoc, dgFunctorCommaComposition_source]
      simp only [dgFunctorCommaSourceComposite, ← Category.assoc, tensorHom_comp_tensorHom,
        dgGluingCommaImageHomMap_source]
      rfl
    exact hl.trans ((dgFunctorCommaSourceComposite_image R C E F X Y Z).trans hr.symm)
  · have hl : (dgFunctorCommaComposition R C E F X Y Z ≫ aXZ) ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) IX IZ =
      dgFunctorCommaReplacementComposite R C E F X Y Z := by
      rw [Category.assoc, dgGluingCommaImageHomMap_replacement,
        dgFunctorCommaComposition_replacement]
    have hr : ((aXY ⊗ₘ aYZ) ≫ dgFunctorCommaComposition R E E (DGFunctor.id E) IX IY IZ) ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) IX IZ =
      dgFunctorCommaReplacementComposite R C E F X Y Z := by
      rw [Category.assoc, dgFunctorCommaComposition_replacement]
      simp only [dgFunctorCommaReplacementComposite, ← Category.assoc, tensorHom_comp_tensorHom,
        dgGluingCommaImageHomMap_replacement]
      rfl
    exact hl.trans hr.symm
  · rw [dgGluingCommaImageHomComparison, dgFunctorCommaComposition_comparison,
      dgFunctorCommaHomComparison_precompose, dgFunctorCommaComposition_comparison,
      dgGluingCommaImageCompositePrimitive]

omit X Y Z in
def dgGluingCommaImageFunctor : DGFunctor R (DGFunctorCommaObject R C E F)
    (DGFunctorCommaObject R E E (DGFunctor.id E)) where
  obj := dgGluingCommaImageObject R C E F
  map := dgGluingCommaImageHomMap R C E F
  map_id := dgGluingCommaImageHomMap_identity R C E F
  map_comp := dgGluingCommaImageHomMap_composition R C E F

end SerrePositivity.InfinityCategories
