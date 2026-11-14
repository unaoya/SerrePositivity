module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.DiagramBaseFiberFamily

/-!
概要：底の図式を同じ native な図式へ表示変更しても、元の固定終点族の面を保持する。
方針：図式の等式による fiber の表示変更を、正規化した制限の前で相殺する。
規約：元の図式の全族を選び直さない。使われ方：付加辺面の底を同じ native 二単体へ束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 同じ図式の固定終点 fiber の表示変更は、元の coslice の表示変更と可換。 -/
lemma coconeDiagramEqFiber_ι {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (y : X _⦋0⦌) :
    eqToHom (congrArg (fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace s y) h) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) := by
  subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 図式の表示変更後の正規化した同じ面の制限は、元の正規化制限そのものである。 -/
lemma normalizedCoconeRestrictionFiber_diagramEq {K L X : SSet.{u}}
    {p q : K ⟶ X} (h : p = q) (i : L ⟶ K) (s : L ⟶ X)
    (hp : i ≫ p = s) (hq : i ≫ q = s) (y : X _⦋0⦌) :
    eqToHom (congrArg (fun d ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace d y) h) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber q i hq y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber p i hp y := by
  subst q
  simp only [eqToHom_refl, Category.id_comp]

/-- native 表示へ移した同じ底の全族の面は、元の部分図式の底に厳密に一致する。 -/
lemma diagramBaseFiberFamily_restrict_of_eq {K L E B T : SSet.{u}}
    (q : E ⟶ B) (t : K ⟶ E) (n : K ⟶ B) (hn : t ≫ q = n)
    (y : B _⦋0⦌) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t)
    (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) ≫ q = SSet.const y)
    (i : L ⟶ K) (s : L ⟶ E) (hs : i ≫ t = s) (hb : i ≫ n = s ≫ q) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily q s y (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction t i hs)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramNormalizedRestriction_fixed q t i s hs y a ha) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily q t y a ha ≫
        eqToHom (congrArg (fun d ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace d y) hn)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber n i hb y := by
  rw [Category.assoc, normalizedCoconeRestrictionFiber_diagramEq hn i (s ≫ q)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hs)) hb y]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_restrict q t y a ha i s hs

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
