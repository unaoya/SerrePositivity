module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.LocalizationArrowCoefficients

/-!
# 同じ局所化生成射の恒等の法則

概要：HTT §1.2.3 のホモトピー圏で、指定された恒等生成辺の類は恒等。
方針：元の源の全関手と指定生成射の自然性の四角形を使う。
規約：実際の生成辺の類を計算する。
使われ方：M10 の円筒の交差辺の射影の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
variable (C : RelativeCategory.{u})

/-- 概要：同じ恒等生成辺の類は恒等射（HTT §1.2.3）。
方針：源の恒等射の保存を同じ頂点比較で共役する。
規約：別の恒等辺との厳密等号は主張しない。使われ方：弱円筒の射影の成分。 -/
lemma localizationStrictHom_id (X : C.category) :
    SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C (𝟙 X))) =
      𝟙 _ := by
  have h := localizationStrictSourceIso_naturality C (𝟙 X)
  rw [nerve.edgeMk_id, SSet.HomotopyCategory.homMk_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  apply (cancel_epi (localizationStrictSourceIso C X).hom).mp
  simpa only [Category.comp_id] using h.symm

attribute [cite HTT "1.2.3" (partial := component)
  "この相対局所化の指定された恒等生成辺について、元の全源関手との比較から類を計算する。"]
  localizationStrictHom_id

end SerrePositivity.EInfinity.Modules
