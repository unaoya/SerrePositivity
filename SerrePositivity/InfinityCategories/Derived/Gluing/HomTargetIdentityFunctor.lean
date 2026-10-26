module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityComma
/-! 元二脚から恒等二脚への dg 関手。全 Hom の三成分を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "I" => dgHomGluingBimodule R E E E (DGFunctor.id E) (DGFunctor.id E)
local notation "T" => dgGluingHomTargetIdentityObject R C D E p q
local notation "H" => dgGluingHomTargetIdentityHomMap R C D E p q
local notation "K" => dgGluingHomTargetToComma R E E E (DGFunctor.id E) (DGFunctor.id E)
local notation "J" => dgGluingHomTargetIdentityCommaFunctor R C D E p q

lemma dgGluingHomComparison_precompose
    (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
    (A B : Complex R) (a : A ⟶ B) (b : B ⟶ dgGluingHomComplex R C D M X Y) :
    dgGluingHomComparison R C D M X Y A (a ≫ b) =
      (Cochain.ofHom a).comp (dgGluingHomComparison R C D M X Y B b) (zero_add _) := by
  dsimp only [dgGluingHomComparison]
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

lemma dgGluingHomTargetIdentityHomMap_comma
    (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :
    H X Y ≫ (K).map (T X) (T Y) = (J).map X Y := by
  apply dgFunctorCommaHom_ext R E E (DGFunctor.id E)
    (dgGluingHomTargetIdentityCommaObject R C D E p q X)
    (dgGluingHomTargetIdentityCommaObject R C D E p q Y) _
  · change (H X Y ≫ dgGluingHomTargetCommaHomMap R E E E
        (DGFunctor.id E) (DGFunctor.id E) (T X) (T Y)) ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          (dgGluingHomTargetCommaObject R E E E (DGFunctor.id E) (DGFunctor.id E) (T X))
          (dgGluingHomTargetCommaObject R E E E (DGFunctor.id E) (DGFunctor.id E) (T Y)) =
      (dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
        dgGluingCommaImageHomMap R D E q _ _) ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          (dgGluingCommaImageObject R D E q (dgGluingHomTargetCommaObject R C D E p q X))
          (dgGluingCommaImageObject R D E q (dgGluingHomTargetCommaObject R C D E p q Y))
    rw [Category.assoc, dgGluingHomTargetCommaHomMap_source,
      dgGluingHomTargetIdentityHomMap_right, Category.assoc,
      dgGluingCommaImageHomMap_source]
    change _ = dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
      (dgFunctorCommaSourceHomMap R D E q _ _ ≫ q.map X.right Y.right)
    rw [← Category.assoc, dgGluingHomTargetCommaHomMap_source]
  · change (H X Y ≫ dgGluingHomTargetCommaHomMap R E E E
        (DGFunctor.id E) (DGFunctor.id E) (T X) (T Y)) ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          (dgGluingHomTargetCommaObject R E E E (DGFunctor.id E) (DGFunctor.id E) (T X))
          (dgGluingHomTargetCommaObject R E E E (DGFunctor.id E) (DGFunctor.id E) (T Y)) =
      (dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
        dgGluingCommaImageHomMap R D E q _ _) ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          (dgGluingCommaImageObject R D E q (dgGluingHomTargetCommaObject R C D E p q X))
          (dgGluingCommaImageObject R D E q (dgGluingHomTargetCommaObject R C D E p q Y))
    rw [Category.assoc, dgGluingHomTargetCommaHomMap_replacement]
    simp only [DGFunctor.id, EnrichedFunctor.id_map, Category.comp_id]
    rw [dgGluingHomTargetIdentityHomMap_left, Category.assoc,
      dgGluingCommaImageHomMap_replacement, dgGluingHomTargetCommaHomMap_replacement]
  · change dgFunctorCommaHomComparison R E E (DGFunctor.id E) _ _ _
        (H X Y ≫ dgGluingHomTargetCommaHomMap R E E E
          (DGFunctor.id E) (DGFunctor.id E) (T X) (T Y)) =
      dgFunctorCommaHomComparison R E E (DGFunctor.id E) _ _ _
        (dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
          dgGluingCommaImageHomMap R D E q _ _)
    rw [dgFunctorCommaHomComparison_precompose,
      dgGluingHomTargetCommaHomMap_comparison,
      dgGluingCommaImageHomComparison, dgGluingHomTargetCommaHomMap_comparison]
    have h := dgGluingHomTargetIdentityHomMap_comparison R C D E p q X Y
    dsimp only [dgGluingHomComparison] at h
    exact h

lemma dgGluingIdentityToComma_cancel
    (X Y : DGGluingObject R E E
      (dgHomGluingBimodule R E E E (DGFunctor.id E) (DGFunctor.id E)))
    (A : Complex R) (a b : A ⟶ dgGluingHomComplex R E E I X Y)
    (h : a ≫ (K).map X Y = b ≫ (K).map X Y) : a = b := by
  apply dgGluingHom_ext R E E I X Y A
  · have h' := congrArg (fun t => t ≫ dgFunctorCommaReplacementHomMap R E E
        (DGFunctor.id E) _ _) h
    simp only [Category.assoc, dgGluingHomTargetToComma,
      dgGluingHomTargetCommaHomMap_replacement, DGFunctor.id, EnrichedFunctor.id_map,
      Category.comp_id] at h'
    exact h'
  · have h' := congrArg (fun t => t ≫ dgFunctorCommaSourceHomMap R E E
        (DGFunctor.id E) _ _) h
    simp only [Category.assoc, dgGluingHomTargetToComma,
      dgGluingHomTargetCommaHomMap_source] at h'
    exact h'
  · have h' := congrArg (fun t => dgFunctorCommaHomComparison R E E
        (DGFunctor.id E) _ _ A t) h
    change dgFunctorCommaHomComparison R E E (DGFunctor.id E) _ _ A
        (a ≫ dgGluingHomTargetCommaHomMap R E E E (DGFunctor.id E) (DGFunctor.id E) X Y) =
      dgFunctorCommaHomComparison R E E (DGFunctor.id E) _ _ A
        (b ≫ dgGluingHomTargetCommaHomMap R E E E (DGFunctor.id E) (DGFunctor.id E) X Y) at h'
    rw [dgFunctorCommaHomComparison_precompose, dgFunctorCommaHomComparison_precompose,
      dgGluingHomTargetCommaHomMap_comparison] at h'
    dsimp only [dgGluingHomComparison]
    exact h'

def dgGluingHomTargetToIdentity :
    DGFunctor R (DGGluingObject R C D M) (DGGluingObject R E E I) where
  obj := T
  map := H
  map_id X := by
    apply dgGluingIdentityToComma_cancel R E (T X) (T X) _
    rw [Category.assoc, dgGluingHomTargetIdentityHomMap_comma]
    exact (J).map_id X |>.trans ((K).map_id (T X)).symm
  map_comp X Y Z := by
    apply dgGluingIdentityToComma_cancel R E (T X) (T Z) _
    rw [Category.assoc, dgGluingHomTargetIdentityHomMap_comma,
      Category.assoc, (K).map_comp, tensorHom_comp_tensorHom_assoc]
    rw [dgGluingHomTargetIdentityHomMap_comma, dgGluingHomTargetIdentityHomMap_comma]
    exact (J).map_comp X Y Z

lemma dgGluingHomTargetToIdentity_comma :
    (dgGluingHomTargetToIdentity R C D E p q).comp (K) = J := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  exact dgGluingHomTargetIdentityHomMap_comma R C D E p q X Y

lemma dgGluingHomTargetToIdentity_left :
    (dgGluingHomTargetToIdentity R C D E p q).comp (dgGluingLeft R E E I) =
      (dgGluingLeft R C D M).comp p := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  exact dgGluingHomTargetIdentityHomMap_left R C D E p q X Y

lemma dgGluingHomTargetToIdentity_right :
    (dgGluingHomTargetToIdentity R C D E p q).comp (dgGluingRight R E E I) =
      (dgGluingRight R C D M).comp q := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id, DGFunctor.comp, EnrichedFunctor.comp_map]
  rw [dgGluingRight_map, dgGluingRight_map]
  exact dgGluingHomTargetIdentityHomMap_right R C D E p q X Y

end SerrePositivity.InfinityCategories
