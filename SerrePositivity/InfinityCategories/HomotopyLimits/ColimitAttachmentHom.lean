module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentComparison
public import SerrePositivity.InfinityCategories.F1.CoherentEdgeEquiv

/-!
概要：部分余極限の coherent な比較から、元の単体的圏の実際の頂点間の射を取り出す。
方針：余錐の頂点を通常の対象で表示し、端点を正規化した辺を射へ戻す。
規約：辺をホモトピー類に落とさず、元の辺との厳密な一致を保持する。
使われ方：空間の部分余極限対象の span と、骨格の余極限対象の列の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  {A C : SSet.{max u v}} {p : A ⟶ SimplicialNerve D}

/-- 部分余極限の比較辺を、通常の頂点対象を端点として表示し直す。 -/
def colimitAttachmentNormalizedEdge (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ SimplicialNerve D) (hi : i ≫ F = p) (d : JoinCocone F) :
    (SimplicialNerve D).Edge (coherentNerveVertex (coherentNerveObject c.vertex))
      (coherentNerveVertex (coherentNerveObject d.vertex)) := by
  let e := colimitAttachmentApexEdge c hc i F hi d
  exact ⟨e.edge, e.src_eq.trans (coherentNerveVertex_object c.vertex).symm,
    e.tgt_eq.trans (coherentNerveVertex_object d.vertex).symm⟩

/-- 部分余極限の頂点から、元の余錐の頂点への実際の通常の射。 -/
def colimitAttachmentApexHom (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ SimplicialNerve D) (hi : i ≫ F = p) (d : JoinCocone F) :
    coherentNerveObject c.vertex ⟶ coherentNerveObject d.vertex :=
  coherentNerveEdgeToHom (colimitAttachmentNormalizedEdge c hc i F hi d)

/-- 抽出した通常の射の辺は、脚とともに構成した元の coherent な比較辺そのもの。 -/
lemma colimitAttachmentApexHom_edge (c : JoinCocone p) (hc : IsColimitCone c)
    (i : A ⟶ C) (F : C ⟶ SimplicialNerve D) (hi : i ≫ F = p) (d : JoinCocone F) :
    (coherentNerveEdge (colimitAttachmentApexHom c hc i F hi d)).edge =
      (colimitAttachmentApexEdge c hc i F hi d).edge :=
  congrArg (fun e ↦ e.edge)
    (coherentNerveEdge_hom (colimitAttachmentNormalizedEdge c hc i F hi d))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
