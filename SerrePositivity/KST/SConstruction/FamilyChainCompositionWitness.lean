module
public import SerrePositivity.KST.SConstruction.FamilyHomotopyChains
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 元の全区間を記録する有限列の実合成証人
概要：有限補正列を一本の実円柱へまとめるとき、元の各区間と各合成三角形を保存する。
方針：元の列の帰納構造と同じ合成木を、全二単体のデータで保持する。
規約：単に合成類が等しいことや、代表の存在だけを結果としない。
使われ方：貼り合わせ複体の両境界から全段比較円柱を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の各区間と各実合成三角形を全て保持する、有限列の合成木。 -/
inductive FamilyChainCompositionWitness {U E : SSet.{u}} :
    {f g : U ⟶ E} → FamilyHomotopyChain f g → SSet.Homotopy f g → Type u
  | nil (f : U ⟶ E) : FamilyChainCompositionWitness (.nil f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f)
  | cons {f g h : U ⟶ E} (a : SSet.Homotopy f g) (tail : FamilyHomotopyChain g h)
      {tailComposite : SSet.Homotopy g h}
      (tailWitness : FamilyChainCompositionWitness tail tailComposite)
      {composite : SSet.Homotopy f h}
      (triangle : SSet.Edge.CompStruct
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy tailComposite))
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy composite))) :
      FamilyChainCompositionWitness (.cons a tail) composite

/-- 合成木に記録した元の全実区間を順に取り出す。 -/
def familyChainCompositionInputTrace {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) : List (U ⊗ (Δ[1] : SSet.{u}) ⟶ E) :=
  match w with
  | .nil _ => []
  | .cons a _ tailWitness _ => a.h :: familyChainCompositionInputTrace tailWitness

/-- 合成木は元の全 trace と同じ全区間・順序を厳密に保持する。 -/
lemma familyChainCompositionInputTrace_eq {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    familyChainCompositionInputTrace w = familyHomotopyChainTrace c := by
  induction w with
  | nil => rfl
  | cons a tail tailWitness triangle ih =>
      exact congrArg (a.h :: ·) ih

/-- 各合成の全二単体族を、同じ順に取り出す。 -/
def familyChainCompositionTriangles {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) : List (U ⊗ (Δ[2] : SSet.{u}) ⟶ E) :=
  match w with
  | .nil _ => []
  | .cons _ _ tailWitness triangle =>
      uncurry (SSet.yonedaEquiv.symm triangle.simplex) ::
        familyChainCompositionTriangles tailWitness

end SerrePositivity.KST.SConstruction
