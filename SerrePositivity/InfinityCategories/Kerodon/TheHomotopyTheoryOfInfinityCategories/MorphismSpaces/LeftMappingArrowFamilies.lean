module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingArrow
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaHomotopySquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：F(x)→y の任意の族と非定値の端点のホモトピーを相互に表示する。
方針：comma の表示を始域の引き戻しへ制限する。
規約：パラメータは任意の単体集合、両端の関手を定値に制限しない。
使われ方：B1 の自然な矢印比較を全パラメータで検証する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：非定値の端点 a,b とホモトピー F∘a→b は矢印の族を与える。
方針：Y の comma への持ち上げを始域の引き戻しへ移す。
規約：raw なホモトピーを保持する。
使われ方：写像空間のパラメータ族を比較の始域へ送る。 -/
def leftMappingArrowLift {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift (𝟙 Y) (a ≫ F) b
    { h := H.h
      h₀ := H.h₀
      h₁ := by rw [H.h₁]; rfl
      rel := H.rel }) a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source _ _ _ _)

/-- 概要：持ち上げを Y の矢印へ忘れると元のホモトピーの comma 表示。
方針：引き戻しの第一射影。
規約：raw なホモトピーを保持する。
使われ方：表示の両逆の検証。 -/
lemma leftMappingArrowLift_forget {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowLift F a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift (𝟙 Y) (a ≫ F) b
        { h := H.h, h₀ := H.h₀, h₁ := by rw [H.h₁]; rfl, rel := H.rel } :=
  pullback.lift_fst _ _ _

/-- 概要：持ち上げの x 射影は a。
方針：引き戻しの第二射影。
規約：厳密な等式。使われ方：自然な比較の始域条件。 -/
lemma leftMappingArrowLift_source {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowLift F a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F = a :=
  pullback.lift_snd _ _ _

/-- 概要：持ち上げの y 射影は b。
方針：Y の comma への忘却と標的の公式。
規約：厳密な等式。使われ方：自然な比較の標的条件。 -/
lemma leftMappingArrowLift_target {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowLift F a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget, ← Category.assoc, leftMappingArrowLift_forget,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target]

/-- 概要：矢印の族を非定値の端点のホモトピーへ戻す。
方針：Y の comma のホモトピーを取り、始域を引き戻し条件で正規化する。
規約：ホモトピー類を経由しない。
使われ方：自然な比較の raw な図式の回収。 -/
def leftMappingArrowHomotopy {A X Y : SSet.{u}} {F : X ⟶ Y}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F) :
    SSet.Homotopy ((f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F) ≫ F) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)).h₀, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget_source, ← Category.assoc]
    rfl
  h₁ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)).h₁, Category.comp_id]
    rfl
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)).rel

/-- 概要：持ち上げたホモトピーの raw な射は忘却しても変わらない。
方針：comma の表示の両逆を使う。
規約：端点の証明を比較する必要はない。
使われ方：族の対応の回収。 -/
lemma leftMappingArrowLift_homotopy_h {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    (leftMappingArrowHomotopy (leftMappingArrowLift F a b H)).h = H.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (leftMappingArrowLift F a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)).h = _
  rw [leftMappingArrowLift_forget, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h]

/-- 概要：矢印の族は始域と標的と raw なホモトピーで決まる。
方針：引き戻しの両射影と comma の外延性を使う。
規約：端点の射自体の一致を要求する。
使われ方：全パラメータの表示の両逆。 -/
lemma leftMappingArrow_hom_ext {A X Y : SSet.{u}} {F : X ⟶ Y}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F}
    (ha : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F)
    (hb : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F)
    (hH : (leftMappingArrowHomotopy f).h = (leftMappingArrowHomotopy g).h) : f = g := by
  apply pullback.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma_hom_ext
    · exact (cancel_epi (β_ A (Δ[1] : SSet.{u})).hom).1 hH
    · exact hb
  · exact ha

/-- 概要：族をホモトピーへ戻して持ち上げると元の族。
方針：始域・標的・raw なホモトピーを全て回収する。
規約：射として厳密な等式。
使われ方：自然な矢印比較の検証。 -/
lemma leftMappingArrowLift_homotopy {A X Y : SSet.{u}} {F : X ⟶ Y}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F) :
    leftMappingArrowLift F (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F)
      (leftMappingArrowHomotopy f) = f := by
  apply leftMappingArrow_hom_ext
  · exact leftMappingArrowLift_source _ _ _ _
  · exact leftMappingArrowLift_target _ _ _ _
  · exact leftMappingArrowLift_homotopy_h _ _ _ _

/-- 概要：矢印の族のホモトピー表示はパラメータの前合成に自然。
方針：comma の表示の前合成自然性を用いる。
規約：raw なホモトピーの等式。
使われ方：自然な比較の族への作用の検証。 -/
lemma leftMappingArrowHomotopy_precomp_h {A B X Y : SSet.{u}} {F : X ⟶ Y}
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F) :
    (leftMappingArrowHomotopy (i ≫ f)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (leftMappingArrowHomotopy f).h := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp i (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)

/-- 概要：矢印の族への持ち上げはパラメータの前合成と可換。
方針：始域・標的・ホモトピーの三データを比較する。
規約：任意のパラメータの射 i。
使われ方：単位を入力に含めない自然な対応の具体的な族の作用。 -/
lemma leftMappingArrowLift_precomp {A B X Y : SSet.{u}} (F : X ⟶ Y)
    (i : A ⟶ B) (a : B ⟶ X) (b : B ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowLift F (i ≫ a) (i ≫ b) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) =
      i ≫ leftMappingArrowLift F a b H := by
  apply leftMappingArrow_hom_ext
  · rw [leftMappingArrowLift_source, Category.assoc, leftMappingArrowLift_source]
  · rw [leftMappingArrowLift_target, Category.assoc, leftMappingArrowLift_target]
  · rw [leftMappingArrowLift_homotopy_h, leftMappingArrowHomotopy_precomp_h,
      leftMappingArrowLift_homotopy_h]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
