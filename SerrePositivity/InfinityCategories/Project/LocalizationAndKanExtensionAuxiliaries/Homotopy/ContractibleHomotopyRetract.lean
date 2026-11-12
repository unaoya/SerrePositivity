module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal

/-!
概要：可縮な Kan 複体のホモトピー retract である Kan 複体の可縮性。
方針：可縮な側で残る合成を恒等射に結び、単体的ホモトピー同値で可縮性を移す。
規約：戻る合成については恒等射からのホモトピーを明示的に受け取る。
使われ方：B1 の導来 fiber の可縮性を comma 写像空間へ移す。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

/-- 概要：可縮な Kan 複体への射がホモトピー retract を持てば始域も可縮。
方針：始域のホモトピーを反転し、終域側の合成を可縮性で恒等射に結ぶ。
規約：始域の Kan 性を明示し、単なる二方向の射の存在からは結論しない。
使われ方：各点の単位比較の同値性から comma の始対象性を導く。 -/
lemma isContractibleKan_of_homotopy_retract {X Y : SSet.{u}} [KanComplex X]
    (f : X ⟶ Y) (g : Y ⟶ X) (H : SSet.Homotopy (𝟙 X) (f ≫ g))
    (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X := by
  have := hY.kanComplex
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (terminal.from Y) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration Y).mp hY
  obtain ⟨K, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration (terminal.from Y) (g ≫ f) (𝟙 Y)
    (terminal.hom_ext _ _)
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f :=
    ⟨g, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H).symm⟩, ⟨K⟩⟩
  exact hf.isContractibleKan_iff.mpr hY

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
