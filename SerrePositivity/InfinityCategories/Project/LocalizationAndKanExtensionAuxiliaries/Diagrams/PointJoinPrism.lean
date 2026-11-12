module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismLastContraction

/-!
概要：点との join から定値写像と恒等写像の間の prism を得る。
方針：既存の joinCylinderMap に左の標準零単体を補う。
規約：時間は第一因子で、時刻零が join の左端、時刻一が右端。
使われ方：始対象を固定した収縮の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：時間の左に標準零単体を補う。
方針：標準零頂点への定値射と区間の恒等射を組にする。
規約：標準零単体をモノイダル単位との定義的同一視で扱わない。
使われ方：join の円柱に時間を埋め込む。 -/
def cofinalPointInterval : (Δ[1] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⊗ Δ[1] :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 _)

/-- 概要：点と B の join へ B の prism を写す。
方針：点を補った時間から既存の join の円柱比較を使う。
規約：時刻零で B の値を忘れる。
使われ方：始対象の錐を収縮へ変換する。 -/
noncomputable def cofinalPointJoinPrism (B : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) B :=
  (cofinalPointInterval ▷ B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] B

/-- 概要：prism の時刻零は点への射の後の左包含。
方針：点を補う操作と端点を交換し joinCylinderMap の零端を計算する。
規約：標準零頂点への定値射を使う。
使われ方：収縮の始点の検査。 -/
lemma cofinalPointJoinPrism_zero (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ cofinalPointJoinPrism B =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) B := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ (cofinalPointInterval ▷ B) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 B) ≫
        (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ B) := rfl
  dsimp only [cofinalPointJoinPrism]
  rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero, ← Category.assoc]
  rfl

/-- 概要：prism の時刻一は右包含。
方針：joinCylinderMap の一端を計算して第二射影を消去する。
規約：B は任意。
使われ方：収縮の終点の検査。 -/
lemma cofinalPointJoinPrism_one (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ cofinalPointJoinPrism B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) B := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ (cofinalPointInterval ▷ B) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 B) ≫
        (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ B) := rfl
  dsimp only [cofinalPointJoinPrism]
  rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one, ← Category.assoc]
  rfl

/-- 概要：点との join への prism は右因子の射に自然。
方針：点を補う操作と因子の射を交換し、既存の円柱比較の自然性を使う。
規約：右因子の射に充填性は不要。
使われ方：指定頂点の全ての定値族を収縮が固定することの検査。 -/
lemma cofinalPointJoinPrism_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (Δ[1] ◁ f) ≫ cofinalPointJoinPrism B =
      cofinalPointJoinPrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) f := by
  have he : (Δ[1] ◁ f) ≫ (cofinalPointInterval ▷ B) =
      (cofinalPointInterval ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 (Δ[0] : SSet.{u})) f := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨t, a⟩
    rfl
  dsimp only [cofinalPointJoinPrism]
  rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality, Category.assoc]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
