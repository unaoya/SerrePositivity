module
public import SerrePositivity.KST.SConstruction.MappingSquareBoundaryData
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition

/-! # 三正方形と三指定三角形からの端点固定の合成比較
概要：元の六セルの境界を使い、三つの適合辺を保持する実三角形を得る。
方針：二つの定数外側辺を消し、共通脚の可逆性で合成式を反映する。
規約：入力の正方形・指定三角形全体を保存し、結論も実三角形として返す。
使われ方：元の合成 prism の適合区間を、入力二射の適合区間の実合成と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 三正方形・三指定三角形とその全境界。外側二辺は指定した恒等辺。 -/
structure ThreeSquareCompatibilityData (E : SSet.{u}) where
  /-- 全正方形の共通始点。 -/
  origin : E _⦋0⦌
  /-- 最初の共有区間の終点。 -/
  left : E _⦋0⦌
  /-- 二番目の共有区間の終点。 -/
  bottom : E _⦋0⦌
  /-- 合成射の適合辺の始点。 -/
  upper : E _⦋0⦌
  /-- 二つの適合辺の共通点。 -/
  middle : E _⦋0⦌
  /-- 合成射の適合辺の終点。 -/
  lower : E _⦋0⦌
  /-- 元の合成射の上脚。 -/
  upperLeg : E.Edge origin upper
  /-- 元の合成射の下脚。 -/
  lowerLeg : E.Edge origin lower
  /-- 最初の元の共有辺。 -/
  leftLeg : E.Edge origin left
  /-- 次の元の共有辺。 -/
  bottomLeg : E.Edge origin bottom
  /-- 前の射の上脚の実後合成。 -/
  firstUpper : E.Edge left upper
  /-- 前の射の下脚の実後合成。 -/
  firstLower : E.Edge left middle
  /-- 後の射の上脚の実前合成。 -/
  secondUpper : E.Edge bottom middle
  /-- 後の射の下脚の実前合成。 -/
  secondLower : E.Edge bottom lower
  /-- 元の合成射の適合辺。 -/
  composite : E.Edge upper lower
  /-- 前の射の元の適合辺の後合成。 -/
  first : E.Edge upper middle
  /-- 後の射の元の適合辺の前合成。 -/
  second : E.Edge middle lower
  /-- 元の最初の正方形。 -/
  firstSquare : MappingSquareBoundaryData upperLeg firstUpper leftLeg (SSet.Edge.id upper)
  /-- 元の中央の正方形。 -/
  middleSquare : MappingSquareBoundaryData bottomLeg firstLower leftLeg secondUpper
  /-- 元の最後の正方形。 -/
  lastSquare : MappingSquareBoundaryData bottomLeg (SSet.Edge.id lower) lowerLeg secondLower
  /-- 合成射の元の指定外側三角形。 -/
  compositeTriangle : SSet.Edge.CompStruct upperLeg composite lowerLeg
  /-- 前の射の元の指定外側三角形の後合成。 -/
  firstTriangle : SSet.Edge.CompStruct firstUpper first firstLower
  /-- 後の射の元の指定外側三角形の前合成。 -/
  secondTriangle : SSet.Edge.CompStruct secondUpper second secondLower

/-- 元の六セルの関係は、共通上脚との前合成後に三適合辺の合成式を与える。 -/
lemma ThreeSquareCompatibilityData.whiskered_relation {E : SSet.{u}}
    (D : ThreeSquareCompatibilityData E) :
    SSet.HomotopyCategory.homMk D.upperLeg ≫
        SSet.HomotopyCategory.homMk D.first ≫ SSet.HomotopyCategory.homMk D.second =
      SSet.HomotopyCategory.homMk D.upperLeg ≫ SSet.HomotopyCategory.homMk D.composite := by
  have h₀ := D.firstSquare.homMk_comp
  have h₁ := D.middleSquare.homMk_comp
  have h₂ := D.lastSquare.homMk_comp
  simp only [SSet.HomotopyCategory.homMk_id, Category.comp_id] at h₀ h₂
  calc
    _ = (SSet.HomotopyCategory.homMk D.leftLeg ≫
        SSet.HomotopyCategory.homMk D.firstUpper) ≫
        SSet.HomotopyCategory.homMk D.first ≫ SSet.HomotopyCategory.homMk D.second := by
      rw [← h₀]
    _ = (SSet.HomotopyCategory.homMk D.leftLeg ≫
        SSet.HomotopyCategory.homMk D.firstLower) ≫
        SSet.HomotopyCategory.homMk D.second := by
      rw [← Category.assoc, Category.assoc _ _ (SSet.HomotopyCategory.homMk D.first),
        SSet.HomotopyCategory.homMk_comp_homMk D.firstTriangle]
    _ = (SSet.HomotopyCategory.homMk D.bottomLeg ≫
        SSet.HomotopyCategory.homMk D.secondUpper) ≫
        SSet.HomotopyCategory.homMk D.second := by rw [h₁]
    _ = SSet.HomotopyCategory.homMk D.bottomLeg ≫
        SSet.HomotopyCategory.homMk D.secondLower := by
      rw [Category.assoc, SSet.HomotopyCategory.homMk_comp_homMk D.secondTriangle]
    _ = SSet.HomotopyCategory.homMk D.lowerLeg := h₂
    _ = _ := (SSet.HomotopyCategory.homMk_comp_homMk D.compositeTriangle).symm


/-- Kan 写像空間では、元の三適合辺そのものを三面に持つ実比較三角形がある。 -/
def ThreeSquareCompatibilityData.comparison {E : SSet.{u}} [KanComplex E]
    (D : ThreeSquareCompatibilityData E) : SSet.Edge.CompStruct D.first D.second D.composite := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge D.upperLeg.toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  letI : IsIso (SSet.HomotopyCategory.homMk D.upperLeg) := h
  have hf : SSet.HomotopyCategory.homMk D.first ≫ SSet.HomotopyCategory.homMk D.second =
      SSet.HomotopyCategory.homMk D.composite :=
    (cancel_epi (SSet.HomotopyCategory.homMk D.upperLeg)).mp D.whiskered_relation
  exact SSet.Edge.CompStruct.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hf).some

end SerrePositivity.KST.SConstruction
