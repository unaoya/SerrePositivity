module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftIntervalFatDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalPrismHomotopy

/-!
概要：左の点を持つ fat join の両端固定ホモトピーを区間模型へ移す。
方針：左の点を補う prism の両端を計算し、一般の prism による移送を使う。
規約：左端は始点の点、右端は終点に定値のパラメータ。
使われ方：Kerodon §4.6.6（Tag 04HY）、左写像空間の比較のホモトピー右逆。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間とパラメータから左に点を持つ fat join へ写す。
方針：円柱に点を補い、fat join の円柱包含を続ける。
規約：通常の join との比較は既存の左 prism になる。
使われ方：Kerodon §4.6.6（Tag 04HY）、左 fat join の図式の区間への制限。 -/
noncomputable def leftIntervalFatPrism (A : SSet.{u}) :
    Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderSection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] A

/-- 概要：左 fat prism の零端は左の点への定値射に続く左包含。
方針：円柱の零端の式と直積の第一射影を使う。
規約：点は標準零単体の唯一の頂点。
使われ方：Kerodon §4.6.6（Tag 04HY）、始点を固定するホモトピー条件。 -/
lemma leftIntervalFatPrism_zero (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ leftIntervalFatPrism A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderSection A =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 A) ≫
        (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ A) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold leftIntervalFatPrism
  rw [← Category.assoc, hz, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero,
    ← Category.assoc, lift_fst]

/-- 概要：左 fat prism の一端はパラメータの右包含。
方針：円柱の一端の式と直積の第二射影を使う。
規約：パラメータを恒等で保つ。
使われ方：Kerodon §4.6.6（Tag 04HY）、終点を固定するホモトピー条件。 -/
lemma leftIntervalFatPrism_one (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ leftIntervalFatPrism A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderSection A =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 A) ≫
        (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ A) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  unfold leftIntervalFatPrism
  rw [← Category.assoc, hz, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one,
    ← Category.assoc, lift_snd, Category.id_comp]

/-- 概要：左 fat prism に通常の join 比較を続けると左の写像空間 prism になる。
方針：円柱比較を使い、点を補う直積の射を計算する。
規約：既存の左 prism との射の等式を与える。
使われ方：Kerodon §4.6.6（Tag 04HY）、coslice fiber の区間比較の回収。 -/
lemma leftIntervalFatPrism_comparison (A : SSet.{u}) :
    leftIntervalFatPrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[0] A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A := by
  unfold leftIntervalFatPrism
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison]
  rfl

/-- 概要：左 fat join の両端固定ホモトピーは区間模型の族のホモトピーを与える。
方針：fat prism の両端の計算を一般の prism のホモトピー移送に適用する。
規約：左右の固定はホモトピーの全時間で要求する。
使われ方：Kerodon §4.6.6（Tag 04HY）、左写像空間の比較のホモトピー右逆。 -/
noncomputable def intervalMappingHomotopyOfLeftFatJoin {A X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X} (H : SSet.Homotopy F G)
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
    (hF : leftIntervalFatPrism A ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
    (hG : leftIntervalFatPrism A ≫ G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x)
    (hy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const y) : SSet.Homotopy f g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingHomotopyOfPrism H (leftIntervalFatPrism A) f g hF hG
  · rw [leftIntervalFatPrism_zero, comp_whiskerRight, Category.assoc, hx,
      ← Category.assoc, whiskerRight_fst, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda, SSet.comp_const]
  · rw [leftIntervalFatPrism_one, hy, SSet.comp_const]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
