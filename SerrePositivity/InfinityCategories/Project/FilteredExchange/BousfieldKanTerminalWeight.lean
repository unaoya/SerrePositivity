module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopy

/-!
概要：終対象 t を持つ添字の反変 Bousfield–Kan 重みは、t へ向かう射の頂点に収縮する。
方針：各 Over 圏のその対象の始対象性から恒等関手への自然変換を取る。
規約：収縮の向きは指定頂点から恒等射。使われ方：terminal な coend の収縮。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：反変重みの Over 圏で t に向かう射に対応する対象。
方針：終対象への射を反転する。
規約：左端は常に t の反対対象。使われ方：重みの収縮の始点。 -/
def terminalWeightPoint (ht : IsTerminal t) (i : I) : Over (Opposite.op i) :=
  Over.mk (ht.from i).op

/-- 概要：選んだ対象は重みの Over 圏の始対象。
方針：任意の左端への射を t の終対象性で一意に選ぶ。
規約：Over の構造射との可換性も終対象性から従う。使われ方：自然な収縮。 -/
def terminalWeightPoint_isInitial (ht : IsTerminal t) (i : I) :
    IsInitial (terminalWeightPoint ht i) :=
  IsInitial.ofUniqueHom (fun a ↦ Over.homMk (ht.from a.left.unop).op (by
    apply Quiver.Hom.unop_inj
    exact ht.hom_ext _ _)) (fun a f ↦ by
      apply Over.OverMorphism.ext
      apply Quiver.Hom.unop_inj
      exact ht.hom_ext _ _)

/-- 概要：指定された始対象から恒等関手への自然変換。
方針：始対象に定値な関手の始対象性を使う。
規約：各成分を独立に選び直さない。使われ方：nerve の実際のホモトピー。 -/
def terminalWeightNatTrans (ht : IsTerminal t) (i : I) :
    (Functor.const (Over (Opposite.op i))).obj (terminalWeightPoint ht i) ⟶ 𝟭 _ :=
  (Functor.isInitialConst _ (terminalWeightPoint_isInitial ht i)).to _

/-- 概要：反変重みを指定された頂点から恒等射へ結ぶ実際のホモトピー。
方針：始対象から恒等関手への自然変換の nerve を取る。
規約：Kan 性を重みに要求しない。使われ方：coend の円柱の構成。 -/
def terminalWeightHomotopy (ht : IsTerminal t) (i : I) :
    SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (terminalWeightPoint ht i)))
      (𝟙 (nerve (Over (Opposite.op i)))) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (terminalWeightNatTrans ht i)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (terminalWeightNatTrans ht i)).h₀,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const]
    rfl
  h₁ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (terminalWeightNatTrans ht i)).h₁]
    change nerveMap (𝟭 (Over (Opposite.op i))) = 𝟙 _
    exact nerveFunctor.map_id (Cat.of (Over (Opposite.op i)))
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
