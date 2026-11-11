module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeOperations

/-! # 選んだ全合成円柱の実像と端点の表示変更
概要：保存済みの合成証人を持つ実円柱の後合成を、元の全列の後合成と照合する。
方針：内部 Hom の後合成関手と各元の合成三角形の式を使う。
規約：円柱を選び直さず、表示変更でも全時刻の元の実射を保持する。
使われ方：保存済み各段円柱の構造射像を全辺路の実比較へ渡す。
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

/-- 端点の表示だけを移し、同じ元の円柱全体を保持する。 -/
def familyHomotopyEndpointTransport {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    (H : SSet.Homotopy f g) (hs : f' = f) (ht : g = g') : SSet.Homotopy f' g' := by
  cases hs
  cases ht
  exact H

/-- 表示の移送で実円柱の全時刻の射は変わらない。 -/
lemma familyHomotopyEndpointTransport_h {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    (H : SSet.Homotopy f g) (hs : f' = f) (ht : g = g') :
    (familyHomotopyEndpointTransport H hs ht).h = H.h := by
  cases hs
  cases ht
  rfl

/-- 元の実合成円柱の後合成は、全実補正列の同じ後合成を表す。 -/
lemma familyChainCompositionWitness_postcomp_class {U E B : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (p : E ⟶ B) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H p)) =
        familyChainCompositeClass (familyHomotopyChainMap c p) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, familyChainCompositionWitness_class w,
    familyChainCompositeClass_map]

/-- 同じ端点表示の移送は、円柱と全列の合成式を保つ。 -/
lemma familyCompositeClass_endpointTransport {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    (H : SSet.Homotopy f g) (c : FamilyHomotopyChain f g)
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      familyChainCompositeClass c) (hs : f' = f) (ht : g = g') :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyHomotopyEndpointTransport H hs ht)) =
    familyChainCompositeClass
      (familyHomotopyChainSourceTransport (familyHomotopyChainTargetTransport c ht) hs) := by
  cases hs
  cases ht
  exact h

end SerrePositivity.KST.SConstruction
