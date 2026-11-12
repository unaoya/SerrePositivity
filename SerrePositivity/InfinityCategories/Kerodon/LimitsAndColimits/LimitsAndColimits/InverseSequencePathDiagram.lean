module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InverseSequenceRelativeLifting

/-!
概要：任意の宇宙の可算図式に、既存の自然な可逆 path 置換を適用する。
方針：可算添字圏を AsSmall で係数の宇宙へ持ち上げ、置換を作って元の添字へ制限する。
規約：既存の HomotopyLimits の実装は読み取り専用で利用する。
使われ方：可算骨格の比較を宇宙零に限定せず構成する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet Opposite
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 可算の添字圏と、係数の宇宙に持ち上げた添字圏との明示的な同値。 -/
def inverseSequenceIndexEquivalence : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ := AsSmall.equiv

/-- 任意の宇宙の可算図式の自然変換の、自然な可逆 path 置換。 -/
def inverseSequencePathDiagram {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) : ℕᵒᵖ ⥤ SSet.{u} :=
  inverseSequenceIndexEquivalence.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacement
    (Functor.whiskerLeft inverseSequenceIndexEquivalence.inverse η)

/-- 添字の宇宙を合わせた可逆 path 置換から、元の始域図式への射影。 -/
def inverseSequencePathProjection {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) :
    inverseSequencePathDiagram η ⟶ F :=
  Functor.whiskerLeft inverseSequenceIndexEquivalence.functor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathProjection
      (Functor.whiskerLeft inverseSequenceIndexEquivalence.inverse η))

/-- 添字の宇宙を合わせた可逆 path 置換から、元の標的図式への終点射影。 -/
def inverseSequencePathEndpoint {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) :
    inverseSequencePathDiagram η ⟶ G :=
  Functor.whiskerLeft inverseSequenceIndexEquivalence.functor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathEndpoint
      (Functor.whiskerLeft inverseSequenceIndexEquivalence.inverse η))

/-- 添字の宇宙を合わせた可逆 path 置換の、元の始域図式上の標準切断。 -/
def inverseSequencePathSection {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) :
    F ⟶ inverseSequencePathDiagram η :=
  Functor.whiskerLeft inverseSequenceIndexEquivalence.functor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection
      (Functor.whiskerLeft inverseSequenceIndexEquivalence.inverse η))

/-- 宇宙を合わせた置換の標準切断は、始域への射影の厳密な右逆。 -/
lemma inverseSequencePathSection_projection {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) :
    inverseSequencePathSection η ≫ inverseSequencePathProjection η = 𝟙 F := by
  apply NatTrans.ext
  funext j
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection (η.app j)

/-- 宇宙を合わせた置換の標準切断と終点の合成は、元の自然変換そのもの。 -/
lemma inverseSequencePathSection_endpoint {F G : ℕᵒᵖ ⥤ SSet.{u}} (η : F ⟶ G) :
    inverseSequencePathSection η ≫ inverseSequencePathEndpoint η = η := by
  apply NatTrans.ext
  funext j
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map (η.app j)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
