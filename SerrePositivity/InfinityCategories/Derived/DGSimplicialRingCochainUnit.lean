module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingCochainProductComponents
/-!
概要：元の Moore 単位から実 cochain 単位鎖写像を構成する。
方針：元の実写像と係数環同型、次数移送を保持して比較する。
規約：単体環の可換性・対象宇宙の縮小を要求しない。使われ方：β5(g)。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory KST.ProExcision
local notation "E" => integerCoefficientModuleFunctor
attribute [-instance] ULift.module in
def simplicialRingDGCochainUnitArrow (A : SimplicialObject RingCat.{u}) :
    ModuleCat.of simplicialRingCoefficient.{u} simplicialRingCoefficient.{u} ⟶
      (simplicialRingNormalizedDGComplex A).X 0 := by
  letI : Module simplicialRingCoefficient ((simplicialRingNormalizedCochain A).X 0) :=
    ((simplicialRingNormalizedDGComplex A).X 0).isModule
  exact ModuleCat.ofHom (LinearMap.toSpanSingleton simplicialRingCoefficient
    ((simplicialRingNormalizedDGComplex A).X 0) (simplicialRingDGCochainOne A))

lemma simplicialRingDGCochainUnitArrow_one (A : SimplicialObject RingCat.{u}) :
    (simplicialRingDGCochainUnitArrow A).hom 1 = simplicialRingDGCochainOne A := by
  change @SMul.smul simplicialRingCoefficient _
    ((simplicialRingNormalizedDGComplex A).X 0).isModule.toSMul 1 _ = _
  exact @one_smul simplicialRingCoefficient _ inferInstance
    ((simplicialRingNormalizedDGComplex A).X 0).isModule.toMulAction _


def simplicialRingDGCochainUnit (A : SimplicialObject RingCat.{u}) :
    SerrePositivity.cochainTensorUnit ⟶ simplicialRingNormalizedDGComplex A :=
  HomologicalComplex.mkHomFromSingle (simplicialRingDGCochainUnitArrow A) (fun k hk ↦ by
    apply (simplicialRingNormalizedDGComplex_positive_zero A k ?_).eq_of_tgt
    change (0 : ℤ) + 1 = k at hk
    omega)

lemma simplicialRingDGCochainUnit_f_zero (A : SimplicialObject RingCat.{u}) :
    (simplicialRingDGCochainUnit A).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (ModuleCat.of simplicialRingCoefficient.{u} simplicialRingCoefficient.{u})).hom ≫
          simplicialRingDGCochainUnitArrow A :=
  HomologicalComplex.mkHomFromSingle_f _ _
end SerrePositivity.InfinityCategories
