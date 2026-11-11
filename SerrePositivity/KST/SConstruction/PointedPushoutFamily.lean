module
public import SerrePositivity.KST.SConstruction.ClosedPushoutHom
public import SerrePositivity.KST.SConstruction.PointedFreeFamily
public import SerrePositivity.KST.Spectra.PointedMappingNaturality

/-! # 同じ点つき押し出しの全 basedHom 族の降下
概要：元の二脚で整合する全単体的な基点固定写像族を、同じ押し出しへ降ろす。
方針：自由点つき表示と右 tensor の押し出し保存を使う。
規約：基点固定条件と全パラメータを保持。使われ方：写像円柱の厳密豊穣関手化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Limits SSet
open Spectra.PointedMapping

/-- basedHom の前合成は、自由点つき表示で同じ閉 Hom の前合成になる。 -/
lemma pointedFreeFamily_closedPre {P : SSet.{u}} {X Y Z : PointedSimplicialSet.{u}}
    (a : P ⟶ (PointedObject.basedHom Y Z).right) (f : X ⟶ Y) :
    pointedFreeFamily (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z) =
      pointedFreeFamily a ≫ (MonoidalClosed.pre f).app Z := by
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact pointedFreeFamily_post a (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f Z)

variable {W X Y Z : PointedSimplicialSet.{u}} {P : SSet.{u}}
  (f : W ⟶ X) (g : W ⟶ Y)

/-- 元の全 basedHom 族の整合条件は、自由点つき表示の同じ整合条件になる。 -/
lemma pointedPushoutFamily_condition
    (a : P ⟶ (PointedObject.basedHom X Z).right)
    (b : P ⟶ (PointedObject.basedHom Y Z).right)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z) :
    pointedFreeFamily a ≫ (MonoidalClosed.pre f).app Z =
      pointedFreeFamily b ≫ (MonoidalClosed.pre g).app Z := by
  rw [← pointedFreeFamily_closedPre a f, ← pointedFreeFamily_closedPre b g, h]

/-- 元の点つき押し出し上の、全パラメータを保つ同じ basedHom 族。 -/
def pointedPushoutFamilyDesc
    (a : P ⟶ (PointedObject.basedHom X Z).right)
    (b : P ⟶ (PointedObject.basedHom Y Z).right)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z) :
    P ⟶ (PointedObject.basedHom (pushout f g) Z).right :=
  PointedObject.adjoinHomEquiv P _
    (closedPushoutHomDesc f g (pointedFreeFamily a) (pointedFreeFamily b)
      (pointedPushoutFamily_condition f g a b h))

/-- 降下の自由点つき表示は、元の閉 Hom の降下そのもの。 -/
lemma pointedPushoutFamilyDesc_free
    (a : P ⟶ (PointedObject.basedHom X Z).right)
    (b : P ⟶ (PointedObject.basedHom Y Z).right)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z) :
    pointedFreeFamily (pointedPushoutFamilyDesc f g a b h) =
      closedPushoutHomDesc f g (pointedFreeFamily a) (pointedFreeFamily b)
        (pointedPushoutFamily_condition f g a b h) :=
  pointedFreeFamily_inverse _

/-- 元の左脚への制限は、同じ全 basedHom 族を回収する。 -/
lemma pointedPushoutFamilyDesc_inl
    (a : P ⟶ (PointedObject.basedHom X Z).right)
    (b : P ⟶ (PointedObject.basedHom Y Z).right)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z) :
    pointedPushoutFamilyDesc f g a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inl f g) Z = a := by
  apply pointedFreeFamily_injective
  rw [pointedFreeFamily_closedPre, pointedPushoutFamilyDesc_free]
  exact closedPushoutHomDesc_inl f g (pointedFreeFamily a) (pointedFreeFamily b)
    (pointedPushoutFamily_condition f g a b h)

/-- 元の右脚への制限は、同じ全 basedHom 族を回収する。 -/
lemma pointedPushoutFamilyDesc_inr
    (a : P ⟶ (PointedObject.basedHom X Z).right)
    (b : P ⟶ (PointedObject.basedHom Y Z).right)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Z) :
    pointedPushoutFamilyDesc f g a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inr f g) Z = b := by
  apply pointedFreeFamily_injective
  rw [pointedFreeFamily_closedPre, pointedPushoutFamilyDesc_free]
  exact closedPushoutHomDesc_inr f g (pointedFreeFamily a) (pointedFreeFamily b)
    (pointedPushoutFamily_condition f g a b h)

/-- 元の両脚への制限は、全 basedHom 族の等号を検出する。 -/
lemma pointedPushoutFamily_ext
    {a b : P ⟶ (PointedObject.basedHom (pushout f g) Z).right}
    (hl : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inl f g) Z =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inl f g) Z)
    (hr : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inr f g) Z =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pushout.inr f g) Z) : a = b := by
  apply pointedFreeFamily_injective
  apply closedPushoutHom_ext f g
  · exact (pointedFreeFamily_closedPre a (pushout.inl f g)).symm.trans
      ((congrArg pointedFreeFamily hl).trans (pointedFreeFamily_closedPre b (pushout.inl f g)))
  · exact (pointedFreeFamily_closedPre a (pushout.inr f g)).symm.trans
      ((congrArg pointedFreeFamily hr).trans (pointedFreeFamily_closedPre b (pushout.inr f g)))

end SerrePositivity.KST.SConstruction
