module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredLifting

/-!
概要：自明 Kan fibrations の filtered 余極限射は自明 Kan fibration。
方針：零次元も含む有限な境界への右持ち上げ性の保存を使う。
規約：余極限射に弱同値性を仮定しない。
使われ方：filtered な Kan 模型の比較の弱同値性。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：自明 Kan fibrations の filtered 図式の余極限射は自明 Kan fibration。
方針：全ての有限境界に対する持ち上げ性を余極限へ移す。
規約：図式の値の Kan 性は不要。使われ方：Kan 模型の比較。 -/
lemma trivialKanFibration_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) [∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app j)]
    {cF : Cocone F} (hF : IsColimit cF) {cG : Cocone G} (hG : IsColimit cG)
    (p : cF.pt ⟶ cG.pt) (hp : ∀ j, cF.ι.app j ≫ p = η.app j ≫ cG.ι.app j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary]
  intro n
  have (j : I) : HasLiftingProperty (boundary n).ι (η.app j) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := η.app j) _ inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hasLiftingProperty_of_filtered_isColimit η hF hG p hp (boundary n).ι

/-- 概要：自然変換の filtered 余極限は成分ごとの自明 Kan fibration 性を保つ。
方針：選ばれた余極限余錐と余極限の射の脚の式を使う。
規約：通常の小圏の strict 図式。使われ方：置換図式の余極限での比較。 -/
instance filteredColimitMap_trivialKanFibration
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) [∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app j)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (colim.map η) :=
  trivialKanFibration_of_filtered_isColimit η (colimit.isColimit F) (colimit.isColimit G)
    (colim.map η) (fun j ↦ colimit.ι_map η j)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
