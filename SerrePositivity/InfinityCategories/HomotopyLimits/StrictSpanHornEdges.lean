module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictSpanPointHomEnd
public import SerrePositivity.InfinityCategories.F1.WeightedCosliceTransport

/-!
概要：持ち上げた span の nerve とホーンの同型で、実際の二本の構造辺を同定する。
方針：一単体を射列として計算し、strict な coherent 図式の辺の公式へ渡す。
規約：辺はホモトピー類に落とさない。使われ方：部分余極限の付加比較辺との厳密な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 形状同型の逆は、ホーンの左辺を持ち上げた span の左構造辺へ写す。 -/
lemma strictSpanHornIso_left_edge :
    horn₂₀.ι₀₁ ≫ strictSpanHornIso.{u, v}.inv =
      SSet.yonedaEquiv.symm (ULift.up
        (nerve.edgeMk (AsSmall.up.map WalkingSpan.Hom.fst)).edge) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply ULift.ext
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · apply ULift.ext
    exact Subsingleton.elim _ _

/-- 形状同型の逆は、ホーンの右辺を持ち上げた span の右構造辺へ写す。 -/
lemma strictSpanHornIso_right_edge :
    horn₂₀.ι₀₂ ≫ strictSpanHornIso.{u, v}.inv =
      SSet.yonedaEquiv.symm (ULift.up
        (nerve.edgeMk (AsSmall.up.map WalkingSpan.Hom.snd)).edge) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply ULift.ext
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · apply ULift.ext
    exact Subsingleton.elim _ _

variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  (F : AsSmall.{u} WalkingSpan ⥤ D)

/-- strict な span のホーン表示の左辺は、元の図式の左構造射の coherent な辺。 -/
lemma strictSpanHornDiagram_left_edge :
    horn₂₀.ι₀₁ ≫ strictSpanHornDiagram (strictCoherentDiagram F) =
      SSet.yonedaEquiv.symm (coherentNerveEdge (F.map
        (AsSmall.up.map WalkingSpan.Hom.fst))).edge := by
  rw [strictSpanHornDiagram, ← Category.assoc, strictSpanHornIso_left_edge,
    SSet.yonedaEquiv_symm_comp, strictCoherentDiagram_edge]

/-- strict な span のホーン表示の右辺は、元の図式の右構造射の coherent な辺。 -/
lemma strictSpanHornDiagram_right_edge :
    horn₂₀.ι₀₂ ≫ strictSpanHornDiagram (strictCoherentDiagram F) =
      SSet.yonedaEquiv.symm (coherentNerveEdge (F.map
        (AsSmall.up.map WalkingSpan.Hom.snd))).edge := by
  rw [strictSpanHornDiagram, ← Category.assoc, strictSpanHornIso_right_edge,
    SSet.yonedaEquiv_symm_comp, strictCoherentDiagram_edge]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
