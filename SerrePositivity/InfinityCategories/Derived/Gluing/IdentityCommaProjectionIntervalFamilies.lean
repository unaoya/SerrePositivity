module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PostNormalizeUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedIntervalImage
public import SerrePositivity.InfinityCategories.Derived.Gluing.PreNormalizeUnitCollarTriangles

/-! # 元の二つの Hom 入力の全区間族

概要：補正三角形の全時間の入力を、元 Hom の二つの鎖射影と厳密に同定する。
方針：宇宙持ち上げを相殺し、実 dg 関手の区間評価と正規化鎖射影の等式を使う。
規約：前正規化を経た入力も元入力へ戻し、端点輸送と全パラメーターを保持する。
使われ方：左右の実補正変形を元の入力付き fiber へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
lemma dgGluingIdentityCommaSourceLift_down :
    (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)).comp
      (dgUniverseLiftDown.{u, max u v, max u v} R E) =
      dgFunctorCommaReplacement R E E (DGFunctor.id E) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change ((((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map x y) ≫ 𝟙 _) ≫ 𝟙 _) ≫
    𝟙 _ = (dgFunctorCommaReplacement R E E (DGFunctor.id E)).map x y
  simp only [Category.comp_id]
lemma dgGluingIdentityCommaTargetLift_down :
    (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)).comp
      (dgUniverseLiftDown.{u, max u v, max u v} R E) =
      dgFunctorCommaSource R E E (DGFunctor.id E) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (((((dgFunctorCommaSource R E E (DGFunctor.id E)).map x y) ≫ 𝟙 _) ≫ 𝟙 _) ≫
    𝟙 _) ≫ 𝟙 _ = (dgFunctorCommaSource R E E (DGFunctor.id E)).map x y
  simp only [Category.comp_id]
variable (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
lemma dgGluingIdentityCommaSourceIntervalFamily_chain :
    dgGluingIdentityCommaSourceIntervalFamily R E X Y f =
    (f ≫ pinchedHomChainMap ((dgFunctorCommaSource R E E (DGFunctor.id E)).map X Y)) ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve R E)
        (Simplex.vertex X.source) (Simplex.vertex Y.source) := by
  apply intervalMappingUncurry_injective
  rw [dgGluingIdentityCommaSourceIntervalFamily, intervalMappingPostOfEq_uncurry]
  rw [← dgNerve.map_comp, dgGluingIdentityCommaTargetLift_down]
  exact (dgGluingFunctorPinchedIntervalImage
    (dgFunctorCommaSource R E E (DGFunctor.id E)) (f := f)).symm


local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "fp" => f ≫ pinchedHomChainMap (D := Q) (E := Q)
  (dgGluingIdentityCommaPreNormalizeHom R E X Y)
def dgGluingIdentityCommaReplacementIntervalFamily : K ⟶ intervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex X.replacement) (Simplex.vertex Y.replacement) :=
  (f ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y)) ≫
    pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex X.replacement) (Simplex.vertex Y.replacement)
lemma dgGluingPreNormalizedReplacementIntervalFamily_eq :
    dgGluingPreNormalizedReplacementIntervalFamily R E X Y f =
    dgGluingIdentityCommaReplacementIntervalFamily R E X Y f := by
  apply intervalMappingUncurry_injective
  rw [dgGluingPreNormalizedReplacementIntervalFamily, intervalMappingPostOfEq_uncurry,
    ← dgNerve.map_comp, dgGluingIdentityCommaSourceLift_down,
    dgGluingIdentityCommaReplacementIntervalFamily]
  have hp : fp ≫ pinchedHomChainMap
      ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map NX Y) =
      f ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y) := by
    rw [Category.assoc, ← pinchedHomChainMap_comp]
    change f ≫ pinchedHomChainMap (dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) NX Y) = _
    rw [dgGluingIdentityCommaPreNormalizeHom_replacement]
    rfl
  have hi := dgGluingFunctorPinchedIntervalImage
    (dgFunctorCommaReplacement R E E (DGFunctor.id E)) (f := fp)
  rw [hp] at hi
  exact hi.symm
lemma dgGluingPostNormalizeUnitCollarTriangleFamily_first_original :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f =
      intervalMappingUncurry (CartesianMonoidalCategory.fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingIdentityCommaReplacementIntervalFamily R E X Y f) := by
  rw [dgGluingPostNormalizeUnitCollarTriangleFamily_first_input,
    dgGluingPreNormalizedReplacementIntervalFamily_eq]
end SerrePositivity.InfinityCategories
