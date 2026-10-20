module

public import SerrePositivity.InfinityCategories.F1.KanDiagramNativeOppositeHomParameter
public import SerrePositivity.InfinityCategories.F1.LeftPointHomReverseComposition

/-!
概要：native な反転 Hom のパラメーターによる一点 Hom 係数の作用を元の作用へ戻す。
方針：反転した評価の curry を内部 Hom の反転同型で表示し、既存の係数比較へ合成する。
規約：全 Hom のパラメーターに Kan 性は要求しない。
使われ方：共通 weighted prism の終点の係数作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

private lemma nativePoint_opTensor_naturality {A B C : SSet.{u}} (k : B ⟶ C) :
    (opTensorIso A B).hom ≫ SSet.opFunctor.map (A ◁ k) =
      (A.op ◁ SSet.opFunctor.map k) ≫ (opTensorIso A C).hom := rfl

/-- native な係数射に沿う反転合成は、元のパラメーター付き一点 Hom の作用そのもの。 -/
lemma nativePointHomComposition_eq_parameterized {X Y : KanObject.{u}} {H : SSet.{u}}
    (f : H ⟶ (ihom X.obj).obj Y.obj) :
    ((SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X)).op ◁
      (f ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X.obj).obj Y.obj)).inv ≫
        SSet.opFunctor.map (oppositeInternalHomIso X.obj Y.obj).hom)) ≫
      (opTensorIso (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))
        (SimplicialCategory.sHom (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))).hom ≫
      SSet.opFunctor.map (eComp SSet pointKanObject
        (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y)) =
    leftPointHomParameterizedMap (uncurry f) := by
  have hc : curry ((oppositeTensorIso X.obj H).inv ≫
      SSet.opFunctor.map (uncurry f)) =
    SSet.opFunctor.map f ≫ (oppositeInternalHomIso X.obj Y.obj).hom := by
    apply uncurry_injective
    rw [uncurry_curry, oppositeInternalHom_map_uncurry]
    rfl
  rw [leftPointHomParameterizedMap, hc]
  have hn := SSet.opFunctorCompOpFunctorIso.inv.naturality f
  change f ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X.obj).obj Y.obj)).inv =
    (SSet.opFunctorCompOpFunctorIso.app H).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map f) at hn
  have hp : f ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X.obj).obj Y.obj)).inv ≫
      SSet.opFunctor.map (oppositeInternalHomIso X.obj Y.obj).hom =
    (SSet.opFunctorCompOpFunctorIso.app H).inv ≫ SSet.opFunctor.map
      (SSet.opFunctor.map f ≫ (oppositeInternalHomIso X.obj Y.obj).hom) := by
    rw [SSet.opFunctor.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun z => z ≫ SSet.opFunctor.map (oppositeInternalHomIso X.obj Y.obj).hom) hn
  rw [hp]
  let A := SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X)
  let k := SSet.opFunctor.map f ≫ (oppositeInternalHomIso X.obj Y.obj).hom
  have ht : (oppositeTensorIso A H.op).inv ≫ SSet.opFunctor.map (A ◁ k) =
      (A.op ◁ SSet.opFunctor.map k) ≫
        (opTensorIso A (SimplicialCategory.sHom
          (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))).hom :=
    nativePoint_opTensor_naturality k
  rw [SSet.opFunctor.map_comp
    (((ihom pointKanObject.obj).obj X.obj.op) ◁ k)
    (MonoidalClosed.comp pointKanObject.obj X.obj.op Y.obj.op)]
  have he := congrArg (fun z => (A.op ◁ (SSet.opFunctorCompOpFunctorIso.app H).inv) ≫
    z ≫ SSet.opFunctor.map (eComp SSet pointKanObject
      (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))) ht
  dsimp only [A, k, SimplicialCategory.sHom, eComp, kanObject_simplicialCategory,
    kanObject_enrichedCategory, EnrichedCategory.Hom, EnrichedCategory.comp,
    kanObjectOpFunctor] at he ⊢
  simpa only [whiskerLeft_comp, Category.assoc] using he.symm

/-- 標準係数の逆同型を続けると、native な反転合成は元の同じ全 Hom の評価を回収する。 -/
lemma nativePointHomComposition_coefficient {X Y : KanObject.{u}} {H : SSet.{u}}
    (f : H ⟶ (ihom X.obj).obj Y.obj) :
    (((SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X)).op ◁
      (f ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X.obj).obj Y.obj)).inv ≫
        SSet.opFunctor.map (oppositeInternalHomIso X.obj Y.obj).hom)) ≫
      (opTensorIso (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))
        (SimplicialCategory.sHom (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))).hom ≫
      SSet.opFunctor.map (eComp SSet pointKanObject
        (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y))) ≫
      (pointedSpaceLeftCoefficientIso Y).inv =
    ((pointedSpaceLeftCoefficientIso X).inv ▷ H) ≫ uncurry f := by
  rw [nativePointHomComposition_eq_parameterized]
  exact leftPointHomParameterizedMap_comparison (uncurry f)

end SerrePositivity.InfinityCategories
