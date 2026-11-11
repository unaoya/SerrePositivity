module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapUnitLoopDomains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativeHomotopyEdgeClass
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-! # 終辺の厳密単位退化から実単位閉路の零性

概要：終辺単位三角形が全体で退化する場合、同じ正方形の実閉路は恒等射の類を持つ。
方針：全正方形の退化を区間写像空間へ戻し、元実閉路の辺を比較する。
規約：全時間の等式を使い、端点一致だけでは代用しない。
使われ方：D の第二入力の厳密単位則を実六片の右単位辺へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
lemma dgGluingTerminalUnitConeFamily_degenerate_evaluate {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl b).h := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily_collapse,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  rfl

lemma dgGluingTerminalUnitLoop_homMk_id {K Z : SSet.{u}} {x y : Z _⦋0⦌}
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (l : SSet.Homotopy b b)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry l.h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry b) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  have he : l.h = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl b).h :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
      (h.trans (dgGluingTerminalUnitConeFamily_degenerate_evaluate b))
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl b) := by
    apply Truncated.Edge.ext
    exact congrArg (fun f => SSet.yonedaEquiv (curry f)) he
  rw [he', _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
