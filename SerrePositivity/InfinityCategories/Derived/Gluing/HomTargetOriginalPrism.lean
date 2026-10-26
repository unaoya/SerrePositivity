module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNerveStructure
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedIntervalImage
/-!
概要：元終域の前正規化 cube の元面を、指定 augmentation 全族へ戻す。
方針：恒等 comma への像関手の全 prism 自然性と Hom 全族の自然性を合成する。
規約：元面は頂点・辺だけでなく全区間族として回収する。
使われ方：元 lax Hom 比較を正規化された同じ係数 path へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "G" => DGGluingObject R C D M

lemma dgGluingHomTargetIdentityCommaFunctor_augmentation :
    (Δ[1] ◁ dgNerve.map (dgGluingHomTargetIdentityCommaFunctor R C D E p q)) ≫
      dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
        dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) =
    (β_ (Δ[1] : SSet.{max (u + 1) v}) (dgNerve R G)).hom ≫
      (dgGluingHomTargetAugmentationHomotopy R C D E p q).h := by
  have hmap : dgNerve.map (dgGluingHomTargetIdentityCommaFunctor R C D E p q) =
      dgNerve.map (dgGluingHomTargetToComma R C D E p q) ≫
        dgNerve.map (dgGluingCommaImageFunctor R D E q) :=
    dgNerve.map_comp _ _
  rw [hmap, whiskerLeft_comp, ← Category.assoc,
    Category.assoc (Δ[1] ◁ dgNerve.map (dgGluingHomTargetToComma R C D E p q)),
    dgGluingCommaImageAugmentationPrism.{u, max (u + 1) v} R D E q]
  rfl

variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetHomIntervalEvaluation :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗
      complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
        dgNerve R G :=
  intervalMappingUncurry ((dgGluingHomMappingIso R C D M X Y).inv ≫
    pinchedHomToIntervalMappingSpace (X := dgNerve R G) (Simplex.vertex X) (Simplex.vertex Y))

lemma dgGluingHomTargetPreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1
      (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)))) ≫
        dgGluingHomTargetPreNormalizeCube R C D E p q X Y =
    (Δ[1] ◁ dgGluingHomTargetHomIntervalEvaluation R C D E p q X Y) ≫
      (β_ (Δ[1] : SSet.{max (u + 1) v}) (dgNerve R G)).hom ≫
        (dgGluingHomTargetAugmentationHomotopy R C D E p q).h := by
  have hf := dgGluingFunctorPinchedIntervalImage
    (dgGluingHomTargetIdentityCommaFunctor R C D E p q)
    (dgGluingHomMappingIso R C D M X Y).inv
  change intervalMappingUncurry
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y ≫
        pinchedHomToIntervalMappingSpace _ _) =
    dgGluingHomTargetHomIntervalEvaluation R C D E p q X Y ≫
      dgNerve.map (dgGluingHomTargetIdentityCommaFunctor R C D E p q) at hf
  rw [dgGluingHomTargetPreNormalizeCube, ← Category.assoc,
    dgGluingIdentityCommaPreNormalizeCube_interval_one, hf, whiskerLeft_comp,
    Category.assoc, Category.assoc, dgGluingHomTargetIdentityCommaFunctor_augmentation]

end SerrePositivity.InfinityCategories
