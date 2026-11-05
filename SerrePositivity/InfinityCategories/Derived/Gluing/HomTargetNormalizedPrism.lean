module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationPost
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationHomotopy
/-!
概要：元終域で正規化した Hom の augmentation prism を元の係数 prism へ照合する。
方針：正規化の厳密 cochain 表示と、任意 Hom 鎖写像に対する全 prism 自然性を使う。
規約：第三 cochain と全区間を保ち、頂点ごとの比較で代用しない。
使われ方：元終域の二正規化 cube と主係数 path の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve CochainComplex HomComplex
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "K" => dgGluingHomComplex R C D M X Y
local notation "L" => homObject R E (p.obj X.left) (q.obj Y.right)
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

def dgGluingHomTargetNormalizedPinchedInput :
    complexPinchedSpace.{u, max (u + 1) v} K ⟶
      DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right)) :=
  dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
    R E (p.obj X.left) (q.obj Y.right) K f g h
      (dgGluingHomNegativePrimitive_boundary R C D M X Y)

def dgGluingHomTargetNormalizedRawPinchedInput :
    complexPinchedSpace.{u, max (u + 1) v} K ⟶
      DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right)) :=
  complexPinchedMap.{u, max (u + 1) v}
    (dgGluingHomTargetNormalizedHom R C D E p q X Y) ≫
    (pinchedComplexModelIso (A := R)
      (dgGluingIdentityCommaObject R E (p.obj X.left))
      (dgGluingIdentityCommaObject R E (q.obj Y.right))).inv

section
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetNormalizedPinchedInput_raw :
    dgGluingHomTargetNormalizedPinchedInput R C D E p q X Y =
      dgGluingHomTargetNormalizedRawPinchedInput R C D E p q X Y := by
  unfold dgGluingHomTargetNormalizedPinchedInput dgGluingCochainIdentityCommaPinchedInput
    dgGluingHomTargetNormalizedRawPinchedInput
  apply congrArg (fun φ : K ⟶ dgFunctorCommaHomComplex R E E (DGFunctor.id E)
      (dgGluingIdentityCommaObject R E (p.obj X.left))
      (dgGluingIdentityCommaObject R E (q.obj Y.right)) =>
        complexPinchedMap.{u, max (u + 1) v} φ ≫
          (pinchedComplexModelIso (A := R)
            (dgGluingIdentityCommaObject R E (p.obj X.left))
            (dgGluingIdentityCommaObject R E (q.obj Y.right))).inv)
  exact (dgGluingHomTargetNormalizedHom_eq_cochainLift R C D E p q X Y).symm

end

def dgGluingHomTargetNormalizedPrism :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ complexPinchedSpace.{u, max (u + 1) v} K ⟶
      DGNerve.pinchedHom R E (p.obj X.left) (q.obj Y.right) :=
  (Δ[1] ◁ dgGluingHomTargetNormalizedPinchedInput R C D E p q X Y) ≫
    dgGluingIdentityCommaPinchedPrism R E (p.obj X.left) (q.obj Y.right)

lemma dgGluingHomTargetNormalizedPrism_eq_cochain :
    dgGluingHomTargetNormalizedPrism R C D E p q X Y =
      dgGluingCochainAugmentationPrism.{u, max (u + 1) v} R E (p.obj X.left) (q.obj Y.right) K f g h
        (dgGluingHomNegativePrimitive_boundary R C D M X Y) := by
  rfl

/-- 元終域の正規化 prism の全区間は、同じ二作用と負 primitive の係数 prism。 -/
lemma dgGluingHomTargetNormalizedPrism_coefficient :
    dgGluingHomTargetNormalizedPrism R C D E p q X Y ≫
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).inv =
    dgGluingHomCoefficientAugmentationPrism R C D M X Y := by
  rw [dgGluingHomTargetNormalizedPrism_eq_cochain]
  change dgGluingCochainAugmentationPrism.{u, max (u + 1) v} R E (p.obj X.left) (q.obj Y.right) K f g h
      (dgGluingHomNegativePrimitive_boundary R C D M X Y) ≫
      pinchedHomChainMap (D := E) (E := DGComplexPinchedModel.{u, max (u + 1) v} L)
        (x := p.obj X.left) (y := q.obj Y.right)
        (x' := complexPinchedSource L) (y' := complexPinchedTarget L)
        (complexUnitHomIso L).hom = _
  exact dgGluingCochainAugmentationPrism_post.{u, max (u + 1) v} R E
    (DGComplexPinchedModel.{u, max (u + 1) v} L)
    (p.obj X.left) (q.obj Y.right) (complexPinchedSource L) (complexPinchedTarget L)
    K f g h (dgGluingHomNegativePrimitive_boundary R C D M X Y) (complexUnitHomIso L).hom

end SerrePositivity.InfinityCategories
