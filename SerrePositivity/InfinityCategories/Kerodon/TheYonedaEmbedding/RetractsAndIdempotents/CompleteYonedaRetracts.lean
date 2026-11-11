module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessUniverse
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PresheafClosure

/-!
概要：冪等完備な元の ∞ 圏の Yoneda 本質像は、前層圏内の retract に閉じる。
方針：元の持ち上げた圏の coherent 完備性と、元の Yoneda の充満忠実性を使う。
規約：指定された元の前層を元の表現可能前層と比較し、宇宙を明示する。
使われ方：HTT 5.1.4.8 の前層を介する延長の因子化。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 冪等完備な元の圏の Yoneda 対象の指定 retract は、元の表現可能前層と同型。 -/
lemma yonedaRetract_iso_representable {C : SSet.{u}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) (c : C _⦋0⦌) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction F
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up c))) :
    ∃ c' : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso F
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up c'))) := by
  obtain ⟨⟨c'⟩, hc'⟩ := (hC.ulift).retract_iso_in_image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful C) (ULift.up c) F r
  exact ⟨c', hc'⟩

/-- 冪等完備な元の圏の Yoneda retract 閉包は、元の表現可能前層の本質像そのもの。 -/
lemma isRetractPresheaf_iff_representable_of_complete {C : SSet.{u}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsRetractPresheaf F ↔ ∃ c : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso F
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up c))) := by
  constructor
  · rintro ⟨G, ⟨c, rfl⟩, ⟨r⟩⟩
    exact yonedaRetract_iso_representable hC c F r
  · rintro ⟨c, ⟨e⟩⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isRetractPresheaf_of_retract (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e)
      (_root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.mem_retractClosure ⟨c, rfl⟩)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
