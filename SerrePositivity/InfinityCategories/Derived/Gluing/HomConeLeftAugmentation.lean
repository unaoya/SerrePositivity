module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RepresentableEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeSquareSigns

/-! 左 Hom cone 係数を、同じ第三成分を持つ augmentation の加群 cone 係数と比較する。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
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
local notation "B" => dgGluingCommaObject R C D M Y
local notation "C'" => dgGluingCommaObject R C D M Z
local notation "cf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgGluingToComma R C D M)) f
local notation "L" => CategoryTheory.Functor.map (moduleEvaluation R C X.left)
  (dgGluingCommaClosedReplacementMap R C D M B C' cf)
local notation "G" => CategoryTheory.Functor.map (moduleEvaluation R C X.left)
  (dgGluingCommaClosedSourceMap R C D M B C' cf)
local notation "aY" => CategoryTheory.Functor.map (moduleEvaluation R C X.left)
  (DGFunctorCommaObject.augmentation B)
local notation "aZ" => CategoryTheory.Functor.map (moduleEvaluation R C X.left)
  (DGFunctorCommaObject.augmentation C')
local notation "t" => dgGluingCommaClosedSquareHomotopy R C D M B C' cf X.left
local notation "l" => dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "g" => dgGluingHomConeAction R C D M X Y Z f
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "μ" => dgGluingDifference R C D M X Y
local notation "ν" => dgGluingDifference R C D M X Z
local notation "h" => dgGluingHomConeThird R C D M X Y Z f

/-- 左 Hom cone を、同じ閉左射の代表加群の cone へ評価して移す。 -/
def dgGluingHomConeLeftSourceIso : mappingCone l ≅ mappingCone L :=
  eqToIso (congrArg (fun a : homObject R C X.left Y.left ⟶
    homObject R C X.left Z.left => mappingCone a)
      (dgGluingLeftArrow_evaluate R C D M X Y Z f).symm)

/-- 双加群作用の cone を、同じ閉右射の加群像の cone へ移す。 -/
def dgGluingHomConeLeftTargetIso : mappingCone g ≅ mappingCone G :=
  eqToIso (congrArg (fun a : M.value X.left Y.right ⟶ M.value X.left Z.right => mappingCone a)
    (dgGluingRightArrow_evaluate R C D M X Y Z f).symm)

/-- 左係数は、両端を同じ評価 cone へ移すと、元の augmentation の cone 係数の負となる。 -/
lemma dgGluingHomConeLeftCoefficient_augmentation :
    dgGluingHomConeLeftCoefficient R C D M X Y Z f ≫
      (dgGluingHomConeLeftTargetIso R C D M X Y Z f).hom =
    -((dgGluingHomConeLeftSourceIso R C D M X Y Z f).hom ≫
      dgGluingConeCoefficient R C D M Y Z f X.left) := by
  have hc : δ (-1) 0 t + Cochain.ofHom (aY ≫ G - L ≫ aZ) = 0 :=
    dgGluingCommaClosedSquareHomotopy_equation R C D M B C' cf X.left
  have hn := dgGluingConeSquareNeg_boundary L G aY aZ t hc
  have hμ : biprod.inl ≫ μ = -aY := by
    change biprod.inl ≫ μ = -(moduleEvaluation R C X.left).map
      (dgGluingAugmentation R C D M Y)
    rw [dgGluingDifference_inl, dgGluingAugmentation_evaluate]
  have hν : biprod.inl ≫ ν = -aZ := by
    change biprod.inl ≫ ν = -(moduleEvaluation R C X.left).map
      (dgGluingAugmentation R C D M Z)
    rw [dgGluingDifference_inl, dgGluingAugmentation_evaluate]
  have he := dgGluingConeSquareMap_congr l g (biprod.inl ≫ μ) (biprod.inl ≫ ν)
    ((Cochain.ofHom biprod.inl).comp h (zero_add (-1)))
    (dgGluingConeSquareRestriction_boundary l p g biprod.inl biprod.inl
      (dgGluingHomConeLeft_square R C D M X Y Z f) μ ν h
      (dgGluingHomConeThird_boundary R C D M X Y Z f))
    L G (-aY) (-aZ) (-t) hn
    (dgGluingLeftArrow_evaluate R C D M X Y Z f).symm
    (dgGluingRightArrow_evaluate R C D M X Y Z f).symm hμ hν
    (dgGluingHomConeThird_inl R C D M X Y Z f)
  calc
    _ = (dgGluingHomConeLeftSourceIso R C D M X Y Z f).hom ≫
        dgGluingConeSquareMap L G (-aY) (-aZ) (-t) hn := he
    _ = _ := by
      rw [dgGluingConeSquareMap_neg L G aY aZ t hc hn, Preadditive.comp_neg]
      rfl

end SerrePositivity.InfinityCategories
