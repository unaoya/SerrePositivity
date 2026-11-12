module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource
public import SerrePositivity.KST.Spectra.LoopExchangeOperators

/-!
概要：任意の内側の源と外側二つの Kan 円の smash を、二重 loop の厳密座標で表示する。
方針：二度の curry 同型で、交換・反転・標的後合成を同じ実射として照合する。
規約：内側の源に Kan 性を要求しない。使われ方：通常円を内側にする普遍交換入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.TwoLoopSource

/-- 内側の元の源と外側二つの Kan 円の smash。 -/
abbrev source (S : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  S ⊗ (CirclePower.space.{u} ⊗ CirclePower.space.{u})

/-- 外側二円を交換する元の源の自己射。 -/
def swap (S : PointedSimplicialSet.{u}) : source S ⟶ source S :=
  S ◁ (β_ CirclePower.space.{u} CirclePower.space.{u}).hom

/-- 外側二円のうち内側を反転する元の源の自己射。 -/
def reversal (S : PointedSimplicialSet.{u}) : source S ⟶ source S :=
  S ◁ ((CirclePower.integerPowerMap.{u} (-1)) ▷ CirclePower.space.{u})

/-- 同じ二度の curry による元の写像空間の厳密な同型。 -/
def mappingIso (S Z : PointedSimplicialSet.{u}) :
    PointedObject.basedHom (source S) Z ≅
      LoopExchangePaths.doubleLoop (PointedObject.basedHom S Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (CirclePower.space.{u} ⊗ CirclePower.space.{u}) Z ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u}
      (PointedObject.basedHom S Z)

/-- 同じ内部 Hom と外側二重 loop の標的後合成。 -/
def loopPost (S : PointedSimplicialSet.{u}) {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :
    LoopExchangePaths.doubleLoop (PointedObject.basedHom S Z) ⟶
      LoopExchangePaths.doubleLoop (PointedObject.basedHom S Z') :=
  (ihom CirclePower.space.{u}).map
    ((ihom CirclePower.space.{u}).map ((ihom S).map v))

private lemma closed_post {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (S K : C) {Z Z' : C} (v : Z ⟶ Z') :
    (ihom (S ⊗ (K ⊗ K))).map v ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z').hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z')).hom) =
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) ≫
          (ihom K).map ((ihom K).map ((ihom S).map v)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post, ← Category.assoc]

/-- 元の curry 座標は標的の後合成と厳密に自然。 -/
lemma mappingIso_post (S : PointedSimplicialSet.{u}) {Z Z' : PointedSimplicialSet.{u}}
    (v : Z ⟶ Z') :
    PointedObject.basedHomMap (source S) v ≫ (mappingIso S Z').hom =
      (mappingIso S Z).hom ≫ loopPost S v := closed_post S CirclePower.space.{u} v

private lemma closed_pre_swap {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] (S K Z : C) :
    (MonoidalClosed.pre (S ◁ (β_ K K).hom)).app Z ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) =
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K ((ihom S).obj Z)).hom := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap, ← Category.assoc]

private lemma closed_pre_reversal {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (S K : C) (r : K ⟶ K) (Z : C) :
    (MonoidalClosed.pre (S ◁ (r ▷ K))).app Z ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) =
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) ≫
          (ihom K).map ((MonoidalClosed.pre r).app ((ihom S).obj Z)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left, ← Category.assoc]

/-- 元の源の交換は、同じ二重 loop の交換作用となる。 -/
lemma mappingIso_pre_swap (S Z : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (swap S) Z ≫ (mappingIso S Z).hom =
      (mappingIso S Z).hom ≫ LoopExchangePaths.swap (PointedObject.basedHom S Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact closed_pre_swap S CirclePower.space.{u} Z

/-- 元の源の反転も、同じ二重 loop の反転作用となる。 -/
lemma mappingIso_pre_reversal (S Z : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (reversal S) Z ≫ (mappingIso S Z).hom =
      (mappingIso S Z).hom ≫ LoopExchangePaths.reversal (PointedObject.basedHom S Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  simp only [LoopExchangePaths.reversal]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  let K := CirclePower.space.{u}
  let r := CirclePower.integerPowerMap.{u} (-1)
  change (MonoidalClosed.pre (S ◁ (r ▷ K))).app Z ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) =
    ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom S).obj Z)).hom) ≫
        (ihom K).map ((MonoidalClosed.pre r).app ((ihom S).obj Z))
  exact closed_pre_reversal S K r Z

end SerrePositivity.KST.Spectra.TwoLoopSource
