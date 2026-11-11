module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingCochainProductComponents
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
attribute [-instance] ULift.module in
def simplicialRingDGCochainUnitArrow (A : SimplicialObject RingCat.{u}) :
    ModuleCat.of _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u} _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u} ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X 0 := by
  letI : Module _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedCochain A).X 0) :=
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X 0).isModule
  exact ModuleCat.ofHom (LinearMap.toSpanSingleton _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A))

lemma simplicialRingDGCochainUnitArrow_one (A : SimplicialObject RingCat.{u}) :
    (simplicialRingDGCochainUnitArrow A).hom 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A := by
  change @SMul.smul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X 0).isModule.toSMul 1 _ = _
  exact @one_smul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient _ inferInstance
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X 0).isModule.toMulAction _


def simplicialRingDGCochainUnit (A : SimplicialObject RingCat.{u}) :
    SerrePositivity.cochainTensorUnit ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A :=
  HomologicalComplex.mkHomFromSingle (simplicialRingDGCochainUnitArrow A) (fun k hk ↦ by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A k ?_).eq_of_tgt
    change (0 : ℤ) + 1 = k at hk
    omega)

lemma simplicialRingDGCochainUnit_f_zero (A : SimplicialObject RingCat.{u}) :
    (simplicialRingDGCochainUnit A).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (ModuleCat.of _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u} _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u})).hom ≫
          simplicialRingDGCochainUnitArrow A :=
  HomologicalComplex.mkHomFromSingle_f _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
