module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismIntervalSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationCochainSquare

/-! 元 C・D・M の明示 cochain 四角形を、同じ pinched prism の全区間評価へ照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
local notation "RM" => RightModule R C

lemma dgGluingModuleIdentityAugmentationPrism_eq :
    dgGluingModuleIdentityAugmentationPrism R C =
      dgGluingIdentityCommaAugmentationPrism R RM := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, s⟩
  change ((dgCommaAugmentationPrismSimplex R RM RM (DGFunctor.id RM) s
      (stdSimplex.objEquiv β).toOrderHom).map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R RM)).map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM) = _
  apply Simplex.ext
  change ((dgCommaAugmentationPrismSimplex R RM RM (DGFunctor.id RM) s
      (stdSimplex.objEquiv β).toOrderHom).toSimplexData.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R RM)).map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM) = _
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]
  rfl

variable (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
abbrev dgGluingNativeCochainPinchedParameter : SSet.{max (u + 1) v} :=
  complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)
local notation "HP" => dgGluingNativeCochainPinchedParameter R C D M X Y

lemma dgGluingNativeModuleCochainSquare_interval :
    dgGluingNativeModuleCochainSquare R C D M X Y =
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] HP).inv ≫
        ((β_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1]).hom ▷ HP) ≫
          (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] HP).hom ≫
            (Δ[1] ◁ dgGluingNativeModuleCochainPrism R C D M X Y) ≫
              intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R RM)
                (Simplex.vertex (representable R X.left))
                (Simplex.vertex (M.rightAt Y.right))) := by
  have h := dgGluingIdentityCommaPrismInterval_square R RM
    (representable R X.left) (M.rightAt Y.right)
  rw [← dgGluingModuleIdentityAugmentationPrism_eq R C] at h
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, t, s⟩
  let a := (dgGluingNativeModuleCochainRawInput R C D M X Y).app (Opposite.op ⦋n⦌) s
  have he := congrArg (fun k : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[1] ⊗ DGNerve.pinchedHom R (DGFunctorCommaObject R RM RM (DGFunctor.id RM))
        (dgGluingIdentityCommaObject R RM (representable R X.left))
        (dgGluingIdentityCommaObject R RM (M.rightAt Y.right))) ⟶ dgNerve R RM =>
      k.app (Opposite.op ⦋n⦌) (β, (t, a))) h
  exact he

end SerrePositivity.InfinityCategories
