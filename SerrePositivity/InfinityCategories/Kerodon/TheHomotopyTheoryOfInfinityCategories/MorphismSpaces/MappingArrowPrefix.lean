module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingArrowFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalPrefix

/-!
概要：恒等矢印の族から指定された矢印の族への、始域を固定したホモトピー。
方針：元の矢印を min(t,s) で伸ばし、矢印空間へ持ち上げる。
規約：任意の非定値端点とパラメータを許し、充填や選択を使わない。
使われ方：B1 の coherent 比較の像を単位による合成として読む。

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

/-- 概要：恒等矢印の族の表示は F の時間に定値なホモトピー。
方針：始域の引き戻しから忘れ、comma の恒等矢印の族の表示を回収する。
規約：raw な射の等式。使われ方：伸長の最初の矢印の認識。 -/
lemma leftMappingArrowIdentityFamily_h {X Y : SSet.{u}} (F : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F)).h =
      fst X (Δ[1] : SSet.{u}) ≫ F := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F)).h = _
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowForget F =
      F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily (𝟙 Y) := pullback.lift_fst _ _ _
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily (𝟙 Y))).h :=
      congrArg (fun f : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (𝟙 Y) => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy f).h) hf
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp]
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro z
      rfl

/-- 概要：二つの時刻の最小値で指定矢印の族を伸ばす。
方針：時間写像の四辺のうち矢印方向の二辺を使う。
規約：外側の時刻を含む A×Δ[1] がパラメータ。
使われ方：始域固定の矢印空間内のホモトピーを構成する。 -/
def leftMappingArrowPrefixHomotopy {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    SSet.Homotopy ((fst A (Δ[1] : SSet.{u}) ≫ a) ≫ F) H.h where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime A ≫ H.h
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime_arrow_zero, Category.assoc, H.h₀]
    rfl
  h₁ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime_arrow_one, Category.id_comp]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：指定矢印の族の伸長を矢印空間へ持ち上げる。
方針：始域は a に固定し、標的を H の時刻で動かす。
規約：時間は第二因子。使われ方：coherent 比較の自然性の正方形。 -/
def leftMappingArrowPrefix {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    A ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F (fst A (Δ[1] : SSet.{u}) ≫ a) H.h
    (leftMappingArrowPrefixHomotopy F a b H)

/-- 概要：伸長の始域は全時刻で固定されている。
方針：持ち上げの始域射影公式。
規約：raw な射の等式。使われ方：比較正方形の下辺の退化。 -/
lemma leftMappingArrowPrefix_source {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowPrefix F a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F = fst A Δ[1] ≫ a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source _ _ _ _

/-- 概要：伸長の標的は指定された元のホモトピー。
方針：持ち上げの標的射影公式。
規約：raw な射の等式。使われ方：比較正方形の上辺の回収。 -/
lemma leftMappingArrowPrefix_target {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowPrefix F a b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F = H.h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target _ _ _ _

/-- 概要：伸長の最初は始域の恒等矢印の族。
方針：三つの射影を比べ、最小値の時刻零の式を使う。
規約：矢印空間への射としての等式。
使われ方：比較の恒等矢印の像から抽出した単位の回収。 -/
lemma leftMappingArrowPrefix_start {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    SSet.ι₀ ≫ leftMappingArrowPrefix F a b H = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow_hom_ext
  · rw [Category.assoc, leftMappingArrowPrefix_source,
      SSet.ι₀_fst_assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily_source,
      Category.comp_id]
  · rw [Category.assoc, leftMappingArrowPrefix_target, H.h₀,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily_target]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy_precomp_h,
      leftMappingArrowIdentityFamily_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F _ _ _)).h = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime A ≫ H.h) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime_start, Category.assoc, H.h₀]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl

/-- 概要：伸長の最後は指定した元の矢印の族。
方針：三つの射影を比べ、最小値の時刻一の式を使う。
規約：矢印空間への射としての等式。
使われ方：比較正方形の右辺で元の比較を回収。 -/
lemma leftMappingArrowPrefix_end {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    SSet.ι₁ ≫ leftMappingArrowPrefix F a b H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow_hom_ext
  · rw [Category.assoc, leftMappingArrowPrefix_source,
      SSet.ι₁_fst_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source]
  · rw [Category.assoc, leftMappingArrowPrefix_target, H.h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F _ _ _)).h = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime A ≫ H.h) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalPrefixTime_end, Category.id_comp]

/-- 概要：恒等矢印の族から元の矢印の族への自然なホモトピー。
方針：最小値による伸長と両端の回収を束ねる。
規約：充填も独立な頂点ごとの選択も不要。
使われ方：coherent な比較を単位による合成と照合する。 -/
def leftMappingArrowPrefixPath {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H) where
  h := leftMappingArrowPrefix F a b H
  h₀ := leftMappingArrowPrefix_start F a b H
  h₁ := leftMappingArrowPrefix_end F a b H
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
