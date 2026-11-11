module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback

/-! # 固定した cospan 上の錐の四角形表示

概要：slice の錐を全錐の図式、さらに四角形の図式へ写す。
方針：錐の族の比較写像を全図式に含め、形状同型の逆で前合成する。
規約：普遍性は不要。使われ方：D7 の始点の前合成を四角形全体の射へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- Slice の錐を全錐の関手単体集合へ写す。 -/
def sliceConeDiagramMap {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 全錐図式への比較の零次成分。 -/
lemma sliceConeDiagramMap_vertex {K X : SSet.{u}} (p : K ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (sliceConeDiagramMap p).app (Opposite.op ⦋0⦌) c = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val :=
  congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_app_zero p c)

/-- 固定した cospan の錐を四角形全体の関手単体集合へ写す。 -/
def sliceSquareDiagramMap {X : SSet.{u}} (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  sliceConeDiagramMap p ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app X

/-- 四角形表示の零次成分は形状同型の逆で制限した全錐。 -/
lemma sliceSquareDiagramMap_vertex {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (sliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ c.val) := by
  change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app X).app (Opposite.op ⦋0⦌)
    ((sliceConeDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [sliceConeDiagramMap_vertex]
  rfl

/-- 四角形の引き戻し錐の図式表示は元の四角形。 -/
lemma sliceSquareDiagramMap_pullbackCone {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (sliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F := by
  rw [sliceSquareDiagramMap_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ F)) = _
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
