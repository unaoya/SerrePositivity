module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.PointJoinPrism

/-!
概要：右に点を join した単体集合へ恒等図式から定値図式への prism を写す。
方針：区間を第二因子へ移し、右の標準零単体を補って join の円柱比較を使う。
規約：時刻零は左包含、時刻一は右の点。
使われ方：終対象を固定する収縮と終対象包含の right anodyne 性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：図式と右の点の join へ図式の prism を写す。
方針：対称性で図式と時間を交換し、右に標準零単体を補う。
規約：時間は入力の第一因子。
使われ方：終対象への錐を終点収縮へ変える。 -/
def kanRightPointJoinPrism (B : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B (Δ[0] : SSet.{u}) :=
  lift (β_ (Δ[1] : SSet.{u}) B).hom
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap B Δ[0]

/-- 概要：右点 join の prism の時刻零は左包含。
方針：図式と時間の組を join 円柱の零端へ因子分解する。
規約：図式の値をそのまま保つ。
使われ方：終点収縮の始端の検査。 -/
lemma kanRightPointJoinPrism_zero (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ kanRightPointJoinPrism B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B (Δ[0] : SSet.{u}) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ lift (β_ (Δ[1] : SSet.{u}) B).hom
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
    lift (𝟙 B) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
      (SSet.ι₀ (X := B) ▷ (Δ[0] : SSet.{u})) := rfl
  rw [kanRightPointJoinPrism, ← Category.assoc, he, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero, ← Category.assoc, lift_fst, Category.id_comp]

/-- 概要：右点 join の prism の時刻一は右の点への定値図式。
方針：join 円柱の一端の第二射影を計算する。
規約：標準零頂点を用いる。
使われ方：終点収縮の終端の検査。 -/
lemma kanRightPointJoinPrism_one (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ kanRightPointJoinPrism B =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B (Δ[0] : SSet.{u}) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ lift (β_ (Δ[1] : SSet.{u}) B).hom
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
    lift (𝟙 B) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
      (SSet.ι₁ (X := B) ▷ (Δ[0] : SSet.{u})) := rfl
  rw [kanRightPointJoinPrism, ← Category.assoc, he, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one, ← Category.assoc, lift_snd]

/-- 概要：右点 join の prism は図式の写像に自然。
方針：対称性と右の点の補完を射と交換し、join 円柱の自然性を使う。
規約：任意の単体集合の射を扱う。
使われ方：指定終対象の定値族を全時間で固定する。 -/
lemma kanRightPointJoinPrism_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (Δ[1] ◁ f) ≫ kanRightPointJoinPrism B =
      kanRightPointJoinPrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) := by
  have he : (Δ[1] ◁ f) ≫ lift (β_ (Δ[1] : SSet.{u}) B).hom
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
    lift (β_ (Δ[1] : SSet.{u}) A).hom
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap f (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [kanRightPointJoinPrism, ← Category.assoc, he, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality]
  rw [kanRightPointJoinPrism, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
