module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaCounit

/-!
概要：F(x)→y の矢印とその coherent な族を保持する単体集合。
方針：Y の矢印の始域射影を F に沿って引き戻す。
規約：写像空間の各点の同値や自然な単位はまだ入力しない。
使われ方：B1 の自然な矢印の比較から単位を取り出す始域。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：F(x)→y の矢印を全パラメータで保持する空間。
方針：Y の区間 comma の始域を F に沿って引き戻す。
規約：直積の各頂点の写像空間の寄せ集めではない。
使われ方：自然な写像空間比較の具体的な coherent データ。 -/
noncomputable def leftMappingArrow {X Y : SSet.{u}} (F : X ⟶ Y) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (𝟙 Y)) F

/-- 概要：F の始域の情報を忘れて Y の矢印を取り出す。
方針：引き戻しの第一射影。
規約：矢印の始域は F の像。使われ方：矢印のホモトピーの回収。 -/
noncomputable def leftMappingArrowForget {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingArrow F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (𝟙 Y) := pullback.fst _ _

/-- 概要：矢印 F(x)→y の x への射影。
方針：引き戻しの第二射影。
規約：値域は X。使われ方：自然な比較で固定する始域。 -/
noncomputable def leftMappingArrowSource {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingArrow F ⟶ X := pullback.snd _ _

/-- 概要：矢印 F(x)→y の y への射影。
方針：Y の矢印への射影に標的射影を続ける。
規約：値域は Y。使われ方：自然な比較で固定する標的。 -/
noncomputable def leftMappingArrowTarget {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingArrow F ⟶ Y := leftMappingArrowForget F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget (𝟙 Y)

/-- 概要：忘却した矢印の始域は x に F を適用したもの。
方針：引き戻しの可換条件。
規約：射の厳密な等式。使われ方：族のホモトピーの始点の認識。 -/
lemma leftMappingArrowForget_source {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingArrowForget F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (𝟙 Y) = leftMappingArrowSource F ≫ F :=
  pullback.condition

/-- 概要：矢印の始域射影は inner fibration。
方針：Y の矢印の始域射影の充填性を引き戻す。
規約：Y の quasicategory 性だけを要求する。
使われ方：矢印空間を quasicategory として扱う。 -/
instance leftMappingArrowSource_innerFibration {X Y : SSet.{u}} [Quasicategory Y]
    (F : X ⟶ Y) : InnerFibration (leftMappingArrowSource F) :=
  ⟨innerFibrations.pullback_snd _ _ (InnerFibration.mem (q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (𝟙 Y)))⟩

/-- 概要：quasicategory 間の関手の矢印空間は quasicategory。
方針：始域への inner fibration を使う。
規約：F の fibration 性は不要。使われ方：自然な矢印の比較の圏構造。 -/
instance leftMappingArrow_quasicategory {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (F : X ⟶ Y) : Quasicategory (leftMappingArrow F) :=
  quasicategory_of_innerFibration (leftMappingArrowSource F)

/-- 概要：各 F(x) の恒等矢印からなる族。
方針：Y の恒等矢印の族を F に沿って制限し、引き戻しへ持ち上げる。
規約：自然な単位は入力に含めない。
使われ方：自然な矢印の比較へ渡して単位を取り出す。 -/
noncomputable def leftMappingArrowIdentityFamily {X Y : SSet.{u}} (F : X ⟶ Y) :
    X ⟶ leftMappingArrow F :=
  pullback.lift (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily (𝟙 Y)) (𝟙 X) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily_source, Category.comp_id, Category.id_comp])

/-- 概要：恒等矢印の族の x 射影は恒等関手。
方針：引き戻しの持ち上げの公式。
規約：射の厳密な等式。使われ方：単位の始点の回収。 -/
lemma leftMappingArrowIdentityFamily_source {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingArrowIdentityFamily F ≫ leftMappingArrowSource F = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- 概要：恒等矢印の族の y 射影は F。
方針：引き戻しの持ち上げと恒等矢印の族の標的の公式。
規約：射の厳密な等式。使われ方：単位の終点の回収。 -/
lemma leftMappingArrowIdentityFamily_target {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingArrowIdentityFamily F ≫ leftMappingArrowTarget F = F := by
  simp only [leftMappingArrowTarget, leftMappingArrowForget, leftMappingArrowIdentityFamily,
    pullback.lift_fst_assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily_target, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
