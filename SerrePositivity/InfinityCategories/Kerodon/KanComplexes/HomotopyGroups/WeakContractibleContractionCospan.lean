module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopy

/-!
概要：恒等と定値関手からの共通の収縮から nerve の弱可縮性を得る。
方針：Kan 標的への前合成で二つのホモトピーを可逆にし、点への射の逆を構成する。
規約：元の nerve に Kan 性は要求しない。
使われ方：反対単体圏の対角の各 comma の弱可縮性。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-- 概要：恒等と定値写像からの二つのホモトピーを持つ空間は弱可縮。
方針：Kan 標的への前合成に明示的な同型逆を与える。
規約：元の空間のKan性は要求しない。Kan標的の関手空間で向きを反転する。
使われ方：単体的 comma の収縮による Quillen 判定。 -/
lemma isWeaklyContractible_of_contractionCospan {K : SSet.{u}}
    (v : K _⦋0⦌) (r : K ⟶ K) (h0 : SSet.Homotopy (𝟙 K) r)
    (h1 : SSet.Homotopy (SSet.const v) r) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K := by
  intro Z hZ
  let f := terminal.from K
  let g : (⊤_ SSet.{u}) ⟶ K := SSet.const v
  have hgf : g ≫ f = 𝟙 _ := terminal.hom_ext _ _
  have hfg : f ≫ g = SSet.const v := SSet.comp_const _ _
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoPrecompositionOfHomotopy_kan h1 Z) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoPrecompositionOfHomotopy_kan h0 Z).symm
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre f).app Z) := by
    refine ⟨(pre g).app Z, ⟨?_⟩, ⟨?_⟩⟩
    · rw [← NatTrans.comp_app, ← pre_map, hgf, pre_id, NatTrans.id_app]
    · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app, ← hfg] using e
  exact he.isSimplicialHomotopyEquivalence.mapPiZero_bijective

/-- 概要：恒等と定値関手からの共通の自然変換を持つ圏の nerve は弱可縮。
方針：元の自然変換を nerve の実ホモトピーへ移す。
規約：圏の始対象や終対象の存在を要求しない。
使われ方：反対単体圏の二項対角の comma の収縮。 -/
lemma nerve_isWeaklyContractible_of_contractionCospan
    {C : Type u} [Category.{u} C] (v : C) (T : C ⥤ C)
    (h0 : 𝟭 C ⟶ T) (h1 : (Functor.const C).obj v ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve C) := by
  apply isWeaklyContractible_of_contractionCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex v) (nerveMap T)
  · exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy h0
  · exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy h1

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
