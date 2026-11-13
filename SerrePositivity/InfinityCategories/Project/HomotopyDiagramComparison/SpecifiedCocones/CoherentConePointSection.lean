module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceFamily

/-!
概要：切断空間の点から構成した錐の coslice 切断を、元の点の評価として回収する。
方針：頂点の等式による移送を curry の固定条件へ吸収し、二つの全単射の往復を使う。
規約：点の選択や極限性の仮定を追加せず、既存の全単射そのものを計算する。
使われ方：coend の普遍点から作った錐と、実際の Hom 比較の制限の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 頂点の移送を含む coslice curry は、固定条件を変更した curry に等しい。 -/
lemma sliceUnderCurry_vertex_transport {K X : SSet.{u}} {a b : X _⦋0⦌}
    (h : a = b) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ X)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ F = SSet.yonedaEquiv.symm a)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ F = SSet.yonedaEquiv.symm b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F ha ≫ eqToHom (congrArg
        (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) h) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hb := by
  cases h
  exact Category.comp_id _

/-- 切断の点から構成した錐の正規化した切断は、元の点の実際の評価である。 -/
lemma fixedVertexConeSpaceEquiv_cosliceSection {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) _⦋0⦌)
    (hx : ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv p x).symm b).val.vertex = x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv p x).symm b).val ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hx) =
      inv (fst K (Δ[0] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection, sliceUnderCurry_vertex_transport hx _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv p x).symm b).property]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
    (inv (fst K (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm b))) _ = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry_uncurry _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
