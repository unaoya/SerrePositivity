module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource
public import SerrePositivity.KST.Spectra.LoopExchangeOperators

/-!
概要：三つの Kan 円の smash からの写像を、三重 loop の厳密な座標で表示する。
方針：二度の内部 Hom の curry 同型と源制限の自然性を用いる。
規約：交換・反転は元の源の射。使われ方：交換符号の一つの普遍的な入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.TripleCircle

/-- 内側の一つの円と、交換する外側の二つの円の smash。 -/
abbrev source : PointedSimplicialSet.{u} :=
  CirclePower.space.{u} ⊗ (CirclePower.space.{u} ⊗ CirclePower.space.{u})

/-- 外側の二つの円を交換する、元の三重 smash の自己射。 -/
def swap : source.{u} ⟶ source.{u} :=
  CirclePower.space.{u} ◁ (β_ CirclePower.space.{u} CirclePower.space.{u}).hom

/-- 外側二つのうち内側の円を反転する、元の三重 smash の自己射。 -/
def reversal : source.{u} ⟶ source.{u} :=
  CirclePower.space.{u} ◁
    ((CirclePower.integerPowerMap.{u} (-1)) ▷ CirclePower.space.{u})

/-- 三つの円の射を三重 loop の同じ頂点へ移す、実際の点つき同型。 -/
def mappingIso (Z : PointedSimplicialSet.{u}) :
    PointedObject.basedHom source.{u} Z ≅
      LoopExchangePaths.doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u}
      (CirclePower.space.{u} ⊗ CirclePower.space.{u}) Z ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Z)

/-- 同じ三重 loop の標的への後合成。 -/
def loopPost {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :
    LoopExchangePaths.doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z) ⟶
      LoopExchangePaths.doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z') :=
  (ihom CirclePower.space.{u}).map
    ((ihom CirclePower.space.{u}).map ((ihom CirclePower.space.{u}).map v))

private lemma closed_post {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (K : C) {Z Z' : C} (v : Z ⟶ Z') :
    (ihom (K ⊗ (K ⊗ K))).map v ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z').hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z')).hom) =
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) ≫
          (ihom K).map ((ihom K).map ((ihom K).map v)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post, ← Category.assoc]

/-- 元の curry 座標は、標的への後合成と厳密に自然。 -/
lemma mappingIso_post {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :
    PointedObject.basedHomMap source.{u} v ≫ (mappingIso Z').hom =
      (mappingIso Z).hom ≫ loopPost v :=
  closed_post CirclePower.space.{u} v

private lemma closed_pre_swap {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] (K Z : C) :
    (MonoidalClosed.pre (K ◁ (β_ K K).hom)).app Z ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) =
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K ((ihom K).obj Z)).hom := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap, ← Category.assoc]

private lemma closed_pre_reversal {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (K : C) (r : K ⟶ K) (Z : C) :
    (MonoidalClosed.pre (K ◁ (r ▷ K))).app Z ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) =
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) ≫
          (ihom K).map ((MonoidalClosed.pre r).app ((ihom K).obj Z)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left, ← Category.assoc]

/-- 元の源交換への前合成は、同じ三重 loop の外側二つの交換となる。 -/
lemma mappingIso_pre_swap (Z : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z ≫ (mappingIso Z).hom =
      (mappingIso Z).hom ≫
        LoopExchangePaths.swap (PointedObject.basedHom CirclePower.space.{u} Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact closed_pre_swap CirclePower.space.{u} Z

/-- 元の源反転への前合成は、同じ三重 loop の内側の反転となる。 -/
lemma mappingIso_pre_reversal (Z : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z ≫ (mappingIso Z).hom =
      (mappingIso Z).hom ≫
        LoopExchangePaths.reversal (PointedObject.basedHom CirclePower.space.{u} Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  simp only [LoopExchangePaths.reversal]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  let K := CirclePower.space.{u}
  let r := CirclePower.integerPowerMap.{u} (-1)
  change (MonoidalClosed.pre (K ◁ (r ▷ K))).app Z ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) =
    ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (K ⊗ K) Z).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K ((ihom K).obj Z)).hom) ≫
        (ihom K).map ((MonoidalClosed.pre r).app ((ihom K).obj Z))
  exact closed_pre_reversal K r Z

end SerrePositivity.KST.Spectra.TripleCircle
