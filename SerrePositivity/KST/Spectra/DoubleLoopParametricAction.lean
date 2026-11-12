module

public import SerrePositivity.KST.Spectra.LoopExchangeOperators
public import SerrePositivity.KST.Spectra.PointedParametricPostCurry

/-!
概要：標準の二重 loop の全族作用と、交換・反転に対する厳密自然性を構成する。
方針：同じテンソル curry の全族自然性を使い、源作用を同じ円のテンソルの前合成へ戻す。
規約：区間選択や Kan 性不要。使われ方：元の随伴の全族 trace 比較の端点と射影座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths
variable {P Y Y' : PointedSimplicialSet.{u}} (v : P ⟶ PointedObject.basedHom Y Y')

/-- 元の二つの円への標準 ihomAction を反復した、同じ二重 loop の全族作用。 -/
def doubleParametricPost : doubleLoop Y ⟶ PointedObject.basedHom P (doubleLoop Y') :=
  PointedMapping.parametricPost CirclePower.space.{u}
    (v ≫ PointedMapping.ihomAction CirclePower.space.{u} Y Y')

/-- 同じ二重 loop 族作用は、円のテンソルからの curry と厳密に可換。 -/
lemma tensorIso_parametricPost :
    PointedMapping.parametricPost (CirclePower.space.{u} ⊗ CirclePower.space.{u}) v ≫
      PointedObject.basedHomMap P
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u} Y').hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom ≫
      doubleParametricPost v :=
  PointedMapping.parametricPost_tensor CirclePower.space.{u} CirclePower.space.{u} v

/-- 同じテンソル源作用の二重 loop 表示は、標準の全族作用と厳密に可換。 -/
lemma parametricSourceAction
    (a : CirclePower.space.{u} ⊗ CirclePower.space.{u} ⟶
      CirclePower.space.{u} ⊗ CirclePower.space.{u})
    (r : doubleLoop Y ⟶ doubleLoop Y) (r' : doubleLoop Y' ⟶ doubleLoop Y')
    (h₀ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom ≫ r)
    (h₁ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y' ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u} Y').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso CirclePower.space.{u} CirclePower.space.{u} Y').hom ≫ r') :
    r ≫ doubleParametricPost v = doubleParametricPost v ≫ PointedObject.basedHomMap P r' := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  let e := (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K Y).hom
  let e' := (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K Y').hom
  have hm : PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y') ≫
      PointedObject.basedHomMap P e' =
    PointedObject.basedHomMap P e' ≫ PointedObject.basedHomMap P r' := by
    change (ihom P).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y') ≫ (ihom P).map e' =
      (ihom P).map e' ≫ (ihom P).map r'
    rw [← CategoryTheory.Functor.map_comp, h₁, CategoryTheory.Functor.map_comp]
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K Y).hom).mp
  calc
    e ≫ (r ≫ doubleParametricPost v) =
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y ≫ e) ≫ doubleParametricPost v := by rw [h₀, Category.assoc]
    _ = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y ≫
        (PointedMapping.parametricPost (K ⊗ K) v ≫ PointedObject.basedHomMap P e') := by
      rw [Category.assoc, ← tensorIso_parametricPost]
    _ = PointedMapping.parametricPost (K ⊗ K) v ≫
        (PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y') ≫
          PointedObject.basedHomMap P e') := by
      rw [← Category.assoc, ← PointedMapping.parametricPost_restrict, Category.assoc]
    _ = PointedMapping.parametricPost (K ⊗ K) v ≫
        (PointedObject.basedHomMap P e' ≫ PointedObject.basedHomMap P r') := by rw [hm]
    _ = e ≫ (doubleParametricPost v ≫ PointedObject.basedHomMap P r') := by
      rw [← Category.assoc, tensorIso_parametricPost, Category.assoc]

/-- 元の交換射は標準の二重 loop 全族作用と全単体で厳密に可換。 -/
lemma swap_doubleParametricPost :
    swap Y ≫ doubleParametricPost v =
      doubleParametricPost v ≫ PointedObject.basedHomMap P (swap Y') := by
  apply parametricSourceAction v (β_ CirclePower.space.{u} CirclePower.space.{u}).hom
    (swap Y) (swap Y')
  · rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap _ _ _
  · rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap _ _ _

/-- 元の内側の反転射も標準の二重 loop 全族作用と全単体で厳密に可換。 -/
lemma reversal_doubleParametricPost :
    reversal Y ≫ doubleParametricPost v =
      doubleParametricPost v ≫ PointedObject.basedHomMap P (reversal Y') := by
  apply parametricSourceAction v
    ((CirclePower.integerPowerMap.{u} (-1)) ▷ CirclePower.space.{u}) (reversal Y) (reversal Y')
  · dsimp only [reversal]
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left _ _ _
  · dsimp only [reversal]
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_left _ _ _

end SerrePositivity.KST.Spectra.LoopExchangePaths
