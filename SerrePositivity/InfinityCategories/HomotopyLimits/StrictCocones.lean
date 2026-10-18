module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCoconeIndices
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import Mathlib.CategoryTheory.Limits.Opposites

/-!
概要：通常の余錐から元の coherent nerve 内の native な余錐を構成する。
方針：反対の通常の錐を coherent nerve で表示し、反転後に添字と値域を標準同型で戻す。
規約：図式は双対化で得る表示を明示する。標準の strictCoherentDiagram との一致は別に照合する。
使われ方：HTT 4.2.4.1、極限側から余極限側への共有界面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：反対の strict 図式を反転し、元の添字と値域に戻した coherent な図式。
方針：添字の標準同型、反転した F.op の図式、値域の帰還の同型を合成する。
規約：始域は元の I の nerve の明示的な ULift、値域は元の C の coherent nerve。
使われ方：通常の余錐の native な表示の固定図式。 -/
def strictCoherentCoconeDiagram (F : I ⥤ C) :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C :=
  ((strictCoconeIndexIso.{u, v} I).hom ≫ SSet.opFunctor.map (strictCoherentDiagram F.op)) ≫
    (coherentOppositeReturnIso C).hom

/-- 概要：双対化で得た coherent な図式の頂点は元の F(i) の頂点に一致する。
方針：添字の同型の頂点の式、反対の strict 図式の頂点、値域の帰還の式を合成する。
規約：図式全体の標準表示との一致とは区別して零単体を照合する。
使われ方：実際の元の図式の各対象を保持することの検証。 -/
lemma strictCoherentCoconeDiagram_vertex (F : I ⥤ C) (i : I) :
    (strictCoherentCoconeDiagram F).app _ (ULift.up (nerveVertex i)) =
      coherentNerveVertex (F.obj i) := by
  change (coherentOppositeReturnIso C).hom.app _
    ((SSet.opFunctor.map (strictCoherentDiagram F.op)).app _
      ((strictCoconeIndexIso.{u, v} I).hom.app _ (ULift.up (nerveVertex i)))) = _
  rw [strictCoconeIndexIso_hom_vertex, SSet.opFunctor_map, Equiv.apply_symm_apply]
  simp only [nerveVertex, strictCoherentDiagram_vertex]
  exact coherentOppositeReturnIso_hom_vertex _

/-- 概要：通常の余錐は元の coherent nerve の native な join 余錐を定める。
方針：反対の錐の coherent 表示を反転し、元の添字に制限して値域の同型で戻す。
規約：定義には Kan 性や極限性を要求しない。
使われ方：余積・homotopy 押し出し・逐次 homotopy 余極限の実際の余錐の構成。 -/
def strictCoherentCocone {F : I ⥤ C} (c : Cocone F) :
    JoinCocone (strictCoherentCoconeDiagram F) :=
  coherentCoconePost ((strictCoherentCone c.op).reverseCocone.restrict
    (strictCoconeIndexIso.{u, v} I).hom) (coherentOppositeReturnIso C).hom

/-- 概要：通常の余錐の coherent 表示の頂点は元の余錐の頂点。
方針：添字の制限は右頂点を変えず、反転と値域の帰還の頂点の式を適用する。
規約：元の C の対象 c.pt の標準の coherent nerve の頂点として述べる。
使われ方：余極限対象の台を変更せず native な余錐を公開する。 -/
lemma strictCoherentCocone_vertex {F : I ⥤ C} (c : Cocone F) :
    (strictCoherentCocone c).vertex = coherentNerveVertex c.pt := by
  have hr : (((strictCoherentCone c.op).reverseCocone).restrict
      (strictCoconeIndexIso.{u, v} I).hom).vertex =
        ((strictCoherentCone c.op).reverseCocone).vertex := by
    rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq]
    change SSet.yonedaEquiv (joinInr _ Δ[0] ≫
      (joinMap _ (𝟙 (Δ[0] : SSet.{max u v})) ≫ _)) = _
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
  rw [strictCoherentCocone, coherentCoconePost_vertex, hr, JoinCone.reverseCocone_vertex,
    strictCoherentCone_vertex]
  exact coherentOppositeReturnIso_hom_vertex _

/-- 概要：通常の余錐の native な余極限性は反対の coherent な錐の極限性と同値。
方針：反転した余錐の添字の同型と値域の同型が余極限性を保存・反映することを使う。
規約：C の局所 Kan 性も c の通常の余極限性も前提に要求しない。
使われ方：HTT 4.2.4.1、極限側の Hom 条件から native な余極限を証明する界面。 -/
lemma strictCoherentCocone_isColimit_iff {F : I ⥤ C} (c : Cocone F) :
    IsColimitCone (strictCoherentCocone c) ↔ IsLimitCone (strictCoherentCone c.op) := by
  exact ((isLimitCone_iff_reverseCocone_restrict (strictCoherentCone c.op)
    (strictCoconeIndexIso.{u, v} I).hom).trans
      (coherentCoconePost_isColimit_iff _ (coherentOppositeReturnIso C).hom)).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
