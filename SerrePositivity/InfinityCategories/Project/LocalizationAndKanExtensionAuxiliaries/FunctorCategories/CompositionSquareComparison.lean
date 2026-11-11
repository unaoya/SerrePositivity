module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionSquareCollapse
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionTriangleComparison

/-!
概要：二辺を固定した合成三角形の比較を正方形全体の比較へ移す。
方針：正方形への補完を畳み込みによる前合成として計算する。
規約：右辺の path は元の三角形比較の対角の path そのもの。
使われ方：B1 の比較の両合成のホモトピーを境界経路と同時に構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：同じ二辺を持つ三角形から補完した正方形を比較する。
方針：元の相対ホモトピーを畳み込みで前合成する。
規約：三角形比較の選択を保持する。
使われ方：基準単位三角形から元の正方形へ進む変形の第一部分。 -/
noncomputable def FunctorCompositionTriangle.squareRelativeHomotopy
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T₀).diagram
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T₁).diagram where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ▷ (Δ[1] : SSet.{u})) ≫ (T₀.relativeHomotopy T₁).h
  h₀ := by
    have hn : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ _) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ▷ (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ SSet.ι₀ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    rw [← Category.assoc, hn, Category.assoc, SSet.Homotopy.h₀,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle_eq_fold]
    rfl
  h₁ := by
    have hn : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ _) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ▷ (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ SSet.ι₁ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    rw [← Category.assoc, hn, Category.assoc, SSet.Homotopy.h₁,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle_eq_fold]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：補完した正方形の比較中も上辺は固定される。
方針：畳み込みの上辺の公式と相対比較の後辺の固定を使う。
規約：時間方向の射の等式。
使われ方：標的の辺を保つ比較。 -/
lemma FunctorCompositionTriangle.squareRelativeHomotopy_top
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      (T₀.squareRelativeHomotopy T₁).h = fst _ (Δ[1] : SSet.{u}) ≫ curry r.h := by
  change _ ≫ ((_ ▷ _) ≫ (T₀.relativeHomotopy T₁).h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_top,
    T₀.relativeHomotopy_face T₁ 0 (by decide), T₀.face_zero]

/-- 概要：補完した正方形の比較中も左辺は固定される。
方針：畳み込みの左辺の公式と相対比較の前辺の固定を使う。
規約：時間方向の射の等式。
使われ方：単位成分を保つ比較。 -/
lemma FunctorCompositionTriangle.squareRelativeHomotopy_left
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (T₀.squareRelativeHomotopy T₁).h = fst _ (Δ[1] : SSet.{u}) ≫ curry l.h := by
  change _ ≫ ((_ ▷ _) ≫ (T₀.relativeHomotopy T₁).h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_left,
    T₀.relativeHomotopy_face T₁ 2 (by decide), T₀.face_two]

/-- 概要：補完した正方形の比較の右辺は三角形の対角の比較そのもの。
方針：畳み込みの右辺の公式を使う。
規約：path を取り直さない厳密な等式。
使われ方：正方形全体と導来 fiber の path を同時に照合する。 -/
lemma FunctorCompositionTriangle.squareRelativeHomotopy_right
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (T₀.squareRelativeHomotopy T₁).h = (T₀.diagonalHomotopy T₁).h := by
  change _ ≫ ((_ ▷ _) ≫ (T₀.relativeHomotopy T₁).h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_right]
  rfl

/-- 概要：補完した正方形の比較中も恒等の下辺は固定される。
方針：下辺の畳み込みを最初の頂点で因子分解し、相対比較の前辺を制限する。
規約：全時間で指定関手の頂点に定値。
使われ方：comma 正方形の三つの境界辺を同時に固定する。 -/
lemma FunctorCompositionTriangle.squareRelativeHomotopy_bottom
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      (T₀.squareRelativeHomotopy T₁).h = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  change _ ≫ ((_ ▷ _) ≫ (T₀.relativeHomotopy T₁).h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_bottom]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [T₀.relativeHomotopy_face T₁ 2 (by decide)]
  simp only [whiskerRight_fst_assoc, T₀.vertex_zero, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
