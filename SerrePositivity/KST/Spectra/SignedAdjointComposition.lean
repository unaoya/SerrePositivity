module

public import SerrePositivity.KST.Spectra.ParameterizedExchangeSign
public import SerrePositivity.KST.Spectra.LoopSignComponents
public import SerrePositivity.KST.Spectra.TriangleMappingPost

/-!
概要：二つの随伴構造射の合成と符号を調整した loop の構造射の比較。
方針：Kan 円への制限を交換の自然性で移し、交換の符号と二度の符号反転を打ち消す。
規約：通常の円への制限は実際の射の合成として明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。元のスペクトルから符号を変えた loop 模型への比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二つの Kan loop への射の合成は、符号を変えた loop 構造の随伴と同じ成分となる。
方針：円への制限の自然性で二重 Kan loop に戻し、交換の符号をもう一度の符号反転で打ち消す。
規約：最後の標的 Z に通常の Ω 条件を仮定する。
使われ方：BF 1978 §2、HA §1.4.2。各段の随伴構造射のホモトピー可換性。 -/
theorem signed_adjoint_composition {A Y Z W : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex W.right]
    (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    PointedMapping.componentOf (f ≫
      (ihom CirclePower.space.{u}).map (g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} PointedSimplicialSet.circle.{u} Z).hom ≫
          (ihom PointedSimplicialSet.circle.{u}).map
            (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z)) =
      PointedMapping.componentOf ((f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Y) ≫
        (ihom PointedSimplicialSet.circle.{u}).map g) := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  let C : PointedSimplicialSet.{u} := PointedSimplicialSet.circle.{u}
  let qY := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Y
  let qZ := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z
  let qD := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (PointedObject.basedHom K Z)
  let r := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z
  let h := f ≫ (ihom K).map g
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) K CirclePower.unit.{u} Z
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change (ihom K).map qZ ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K C Z).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K Z).hom ≫ qD at hs
  have hc := ((MonoidalClosed.pre CirclePower.unit.{u}).naturality r).symm
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  change qD ≫ (ihom C).map r = (ihom K).map r ≫ qD at hc
  have hleft : f ≫ (ihom K).map (g ≫ qZ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K C Z).hom ≫ (ihom C).map r =
    ((h ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K Z).hom) ≫ (ihom K).map r) ≫ qD := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc ((ihom K).map qZ) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K C Z).hom
      ((ihom C).map r), hs]
    simp only [Category.assoc]
    rw [hc]
    rfl
  have hright : (f ≫ qY) ≫ (ihom C).map g = h ≫ qD := by
    have hn := ((MonoidalClosed.pre CirclePower.unit.{u}).naturality g).symm
    simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
    change qY ≫ (ihom C).map g = (ihom K).map g ≫ qD at hn
    rw [Category.assoc, hn]
    rfl
  have hflip := omega_exchange_sign_component a ha h
  have hpost := PointedMapping.componentOf_comp_right hflip ((ihom K).map r)
  have htwice := PointedMapping.componentOf_nested_neg_one_twice h
  have hcomp := PointedMapping.componentOf_comp_right (hpost.trans htwice) qD
  rw [hleft, hright]
  exact hcomp

end

end SerrePositivity.KST.Spectra
