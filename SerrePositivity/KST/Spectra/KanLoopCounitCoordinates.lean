module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterNaturality

/-!
概要：Kan 円への内部 Hom の座標を、通常の円で評価する同じ counit 座標へ移す。
方針：通常の円への制限の後、元のテンソル内部 Hom 同型の逆を合成する。
規約：Kan 性不要。使われ方：Kan 随伴比較の元の評価の厳密な座標計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra

/-- Kan 円への二重 Hom を、通常の円で評価した懸垂源の Hom へ戻す元の射。 -/
def kanLoopCounit (T V : PointedSimplicialSet.{u}) :
    PointedObject.basedHom T (PointedObject.basedHom CirclePower.space.{u} V) ⟶
      PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension T) V :=
  PointedObject.basedHomMap T (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} V) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} T V).inv

/-- counit の後に元の同型を戻すと、通常の円への同じ制限そのもの。 -/
@[reassoc]
lemma kanLoopCounit_comparison (T V : PointedSimplicialSet.{u}) :
    kanLoopCounit T V ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} T V).hom =
      PointedObject.basedHomMap T (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} V) := by
  rw [kanLoopCounit, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 源への制限を counit で評価すると、同じ源の懸垂による制限となる。 -/
lemma kanLoopCounit_pre {T U : PointedSimplicialSet.{u}} (i : T ⟶ U)
    (V : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space V) ≫ kanLoopCounit T V =
      kanLoopCounit U V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedSimplicialSet.circle.{u} ◁ i) V := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} T V).hom).1
  rw [Category.assoc, kanLoopCounit_comparison]
  have hn := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource.natural_pre_right PointedSimplicialSet.circle.{u} i V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  rw [Category.assoc, hn, ← Category.assoc, kanLoopCounit_comparison]
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (MonoidalClosed.pre i).app ((ihom CirclePower.space.{u}).obj V) ≫
      (ihom T).map ((MonoidalClosed.pre CirclePower.unit.{u}).app V) =
    (ihom U).map ((MonoidalClosed.pre CirclePower.unit.{u}).app V) ≫
      (MonoidalClosed.pre i).app ((ihom PointedSimplicialSet.circle.{u}).obj V)
  exact ((MonoidalClosed.pre i).naturality ((MonoidalClosed.pre CirclePower.unit.{u}).app V)).symm

end SerrePositivity.KST.Spectra
