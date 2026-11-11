module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFamilies
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.DegenerateFunctorHomSquare

/-!
概要：comma 内のホモトピーを h Fun の関係を表す正方形へ移す。
方針：二つの時間をパラメータの後に並べ、矢印のホモトピーを curry する。
規約：四辺は元の raw なホモトピーそのものを回収する。
使われ方：B1 の余単位比較から右三角恒等式を読む。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma のホモトピーを関手の正方形へ移す。
方針：パラメータの直積の結合子を使い、二つの区間を curry する。
規約：第一座標は comma 内の時間、第二座標は X 内の矢印の時間。
使われ方：四辺の合成の関係。 -/
noncomputable def unitCommaHomotopySquare {A X Y : SSet.{u}} {G : Y ⟶ X}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G} (H : SSet.Homotopy f g) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X :=
  curry ((α_ A (Δ[1] : SSet.{u}) Δ[1]).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy H.h).h)

/-- 概要：正方形の下辺は始域射影によるホモトピーの像。
方針：X 内の矢印の時間を零に制限する。
規約：raw な射の一致。使われ方：基底固定条件による恒等辺の認識。 -/
lemma unitCommaHomotopySquare_bottom {A X Y : SSet.{u}} {G : Y ⟶ X}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G} (H : SSet.Homotopy f g) :
    SSet.ι₀ ≫ unitCommaHomotopySquare H = curry (H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [unitCommaHomotopySquare, uncurry_curry]
  have hc : A ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      (α_ A Δ[1] Δ[1]).inv = SSet.ι₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy H.h).h₀]

/-- 概要：正方形の上辺は標的射影の後に G を続けたホモトピーの像。
方針：X 内の矢印の時間を一に制限する。
規約：raw な射の一致。使われ方：余単位の G による像の認識。 -/
lemma unitCommaHomotopySquare_top {A X Y : SSet.{u}} {G : Y ⟶ X}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G} (H : SSet.Homotopy f g) :
    SSet.ι₁ ≫ unitCommaHomotopySquare H = curry (H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G ≫ G) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [unitCommaHomotopySquare, uncurry_curry]
  have hc : A ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      (α_ A Δ[1] Δ[1]).inv = SSet.ι₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy H.h).h₁, Category.assoc]

/-- 概要：正方形の左辺は始点の comma の図式の矢印のホモトピー。
方針：comma 内の時間零へ制限し、前合成自然性を使う。
規約：代表を選び直さない。使われ方：指定単位の回収。 -/
lemma unitCommaHomotopySquare_left {A X Y : SSet.{u}} {G : Y ⟶ X}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G} (H : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ unitCommaHomotopySquare H =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy f).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [unitCommaHomotopySquare, uncurry_curry]
  have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ (α_ A Δ[1] Δ[1]).inv =
      (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u}) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp, H.h₀]

/-- 概要：正方形の右辺は終点の comma の図式の矢印のホモトピー。
方針：comma 内の時間一へ制限し、前合成自然性を使う。
規約：代表を選び直さない。使われ方：恒等矢印の族の回収。 -/
lemma unitCommaHomotopySquare_right {A X Y : SSet.{u}} {G : Y ⟶ X}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G} (H : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ unitCommaHomotopySquare H =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy g).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [unitCommaHomotopySquare, uncurry_curry]
  have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (α_ A Δ[1] Δ[1]).inv =
      (SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u}) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp, H.h₁]

/-- 概要：comma へ持ち上げたホモトピーは矢印の射影で元に戻る。
方針：uncurry の回収と対称性の二重適用を消す。
規約：raw な射の厳密な一致。使われ方：指定単位と恒等矢印の族の認識。 -/
lemma unitCommaHomotopy_lift_h {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G a b H)).h = H.h := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G a b H) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_uncurry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
