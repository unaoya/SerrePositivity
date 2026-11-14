module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の coherent 冪等完備性は ∞ 圏の同値で保たれる。
方針：逆関手で元の全図式を強く分裂し、絶対余極限と元の可逆二胞体で戻す。
規約：全図式を扱い、ホモトピー圏の自己射の分裂だけで代用しない。
使われ方：元の充満忠実な像への移送と本質像の retract 閉性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全図式の coherent 冪等完備性を、指定した元の ∞ 圏同値で移す。 -/
lemma IsIdempotentComplete.of_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Y := by
  intro d
  obtain ⟨s⟩ := hX (d ≫ e.inv)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((d ≫ e.inv) ≫ e.hom) := (s.map e.hom).hasColimit
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d ≫ e.inv) ≫ e.hom) d := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp d
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplitting_exists_of_hasColimit d ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso hd).mp hs)

/-- 指定した元の ∞ 圏同値は、coherent 冪等完備性を保存・反映する。 -/
@[kerodon 040E]
lemma isIdempotentComplete_iff_of_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Y :=
  ⟨fun h ↦ h.of_equivalence e, fun h ↦ h.of_equivalence e.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.3.6" (partial := direction) "仮定：accessible な小準圏 C（HTT と一致）。結論：C は idempotent complete（同値の必要方向と一致）。一般の accessible C の実 Ind 模型の冪等完備性を同じ全同値で戻す。小 idempotent complete C の accessibility、およびそこからの任意の関手の accessibility は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_of_equivalence
