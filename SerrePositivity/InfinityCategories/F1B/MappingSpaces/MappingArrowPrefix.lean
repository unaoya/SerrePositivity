module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.LeftMappingArrowFamilies
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalPrefix

/-!
概要：恒等矢印の族から指定された矢印の族への、始域を固定したホモトピー。
方針：元の矢印を min(t,s) で伸ばし、矢印空間へ持ち上げる。
規約：任意の非定値端点とパラメータを許し、充填や選択を使わない。
使われ方：B1 の coherent 比較の像を単位による合成として読む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：恒等矢印の族の表示は F の時間に定値なホモトピー。
方針：始域の引き戻しから忘れ、comma の恒等矢印の族の表示を回収する。
規約：raw な射の等式。使われ方：伸長の最初の矢印の認識。 -/
lemma leftMappingArrowIdentityFamily_h {X Y : SSet.{u}} (F : X ⟶ Y) :
    (leftMappingArrowHomotopy (leftMappingArrowIdentityFamily F)).h =
      fst X (Δ[1] : SSet.{u}) ≫ F := by
  change (unitCommaHomotopy
    (leftMappingArrowIdentityFamily F ≫ leftMappingArrowForget F)).h = _
  have hf : leftMappingArrowIdentityFamily F ≫ leftMappingArrowForget F =
      F ≫ unitCommaIdentityFamily (𝟙 Y) := pullback.lift_fst _ _ _
  calc
    _ = (unitCommaHomotopy (F ≫ unitCommaIdentityFamily (𝟙 Y))).h :=
      congrArg (fun f : X ⟶ unitComma (𝟙 Y) => (unitCommaHomotopy f).h) hf
    _ = _ := by
      rw [unitCommaHomotopy_precomp]
      unfold unitCommaIdentityFamily
      rw [unitCommaHomotopy_lift_h]
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
  h := intervalPrefixTime A ≫ H.h
  h₀ := by
    rw [← Category.assoc, intervalPrefixTime_arrow_zero, Category.assoc, H.h₀]
    rfl
  h₁ := by rw [← Category.assoc, intervalPrefixTime_arrow_one, Category.id_comp]; rfl
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
    A ⊗ Δ[1] ⟶ leftMappingArrow F :=
  leftMappingArrowLift F (fst A (Δ[1] : SSet.{u}) ≫ a) H.h
    (leftMappingArrowPrefixHomotopy F a b H)

/-- 概要：伸長の始域は全時刻で固定されている。
方針：持ち上げの始域射影公式。
規約：raw な射の等式。使われ方：比較正方形の下辺の退化。 -/
lemma leftMappingArrowPrefix_source {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowPrefix F a b H ≫ leftMappingArrowSource F = fst A Δ[1] ≫ a :=
  leftMappingArrowLift_source _ _ _ _

/-- 概要：伸長の標的は指定された元のホモトピー。
方針：持ち上げの標的射影公式。
規約：raw な射の等式。使われ方：比較正方形の上辺の回収。 -/
lemma leftMappingArrowPrefix_target {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    leftMappingArrowPrefix F a b H ≫ leftMappingArrowTarget F = H.h :=
  leftMappingArrowLift_target _ _ _ _

/-- 概要：伸長の最初は始域の恒等矢印の族。
方針：三つの射影を比べ、最小値の時刻零の式を使う。
規約：矢印空間への射としての等式。
使われ方：比較の恒等矢印の像から抽出した単位の回収。 -/
lemma leftMappingArrowPrefix_start {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    SSet.ι₀ ≫ leftMappingArrowPrefix F a b H = a ≫ leftMappingArrowIdentityFamily F := by
  apply leftMappingArrow_hom_ext
  · rw [Category.assoc, leftMappingArrowPrefix_source,
      SSet.ι₀_fst_assoc, Category.assoc, leftMappingArrowIdentityFamily_source,
      Category.comp_id]
  · rw [Category.assoc, leftMappingArrowPrefix_target, H.h₀,
      Category.assoc, leftMappingArrowIdentityFamily_target]
  · rw [leftMappingArrowHomotopy_precomp_h, leftMappingArrowHomotopy_precomp_h,
      leftMappingArrowIdentityFamily_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫
      (leftMappingArrowHomotopy (leftMappingArrowLift F _ _ _)).h = _
    rw [leftMappingArrowLift_homotopy_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫ (intervalPrefixTime A ≫ H.h) = _
    rw [← Category.assoc, intervalPrefixTime_start, Category.assoc, H.h₀]
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
    SSet.ι₁ ≫ leftMappingArrowPrefix F a b H = leftMappingArrowLift F a b H := by
  apply leftMappingArrow_hom_ext
  · rw [Category.assoc, leftMappingArrowPrefix_source,
      SSet.ι₁_fst_assoc, leftMappingArrowLift_source]
  · rw [Category.assoc, leftMappingArrowPrefix_target, H.h₁, leftMappingArrowLift_target]
  · rw [leftMappingArrowHomotopy_precomp_h, leftMappingArrowLift_homotopy_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫
      (leftMappingArrowHomotopy (leftMappingArrowLift F _ _ _)).h = _
    rw [leftMappingArrowLift_homotopy_h]
    change (_ ▷ (Δ[1] : SSet.{u})) ≫ (intervalPrefixTime A ≫ H.h) = _
    rw [← Category.assoc, intervalPrefixTime_end, Category.id_comp]

/-- 概要：恒等矢印の族から元の矢印の族への自然なホモトピー。
方針：最小値による伸長と両端の回収を束ねる。
規約：充填も独立な頂点ごとの選択も不要。
使われ方：coherent な比較を単位による合成と照合する。 -/
def leftMappingArrowPrefixPath {A X Y : SSet.{u}} (F : X ⟶ Y)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy (a ≫ F) b) :
    SSet.Homotopy (a ≫ leftMappingArrowIdentityFamily F) (leftMappingArrowLift F a b H) where
  h := leftMappingArrowPrefix F a b H
  h₀ := leftMappingArrowPrefix_start F a b H
  h₁ := leftMappingArrowPrefix_end F a b H
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories
