module

public import SerrePositivity.KST.Spectra.StrictCospanHorn
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-!
概要：任意の coherent cospan を通常の cospan の coherent nerve の表示として復元する。
方針：二辺の実際の射を取り出し、共通終点を面の等式で合わせる。
規約：復元後の図式は元の図式と厳密に等しい。使われ方：Sp の任意の引き戻しの存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CospanShape

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- ホーンの二辺の終点は元の coherent 図式内で厳密に一致する。 -/
lemma common_target (p : (horn 2 2 : SSet.{max u v}) ⟶ SimplicialNerve C) :
    (SimplicialNerve C).δ 0 (SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p)) =
      (SimplicialNerve C).δ 0 (SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, ← Category.assoc, horn₂₂.isPushout.w]

/-- 任意の coherent cospan は通常の射の cospan の表示と厳密に一致する。 -/
lemma exists_presentation (p : (horn 2 2 : SSet.{max u v}) ⟶ SimplicialNerve C) :
    ∃ (E X B : C) (f : E ⟶ B) (g : X ⟶ B),
      strictCospanHornIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ cospan f g) = p := by
  let s := SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p)
  let t := SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((SimplicialNerve C).δ 1 s)
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((SimplicialNerve C).δ 1 t)
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((SimplicialNerve C).δ 0 s)
  let a : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B) :=
    ⟨s, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm⟩
  let b : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B) :=
    ⟨t, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm,
      (common_target p).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm⟩
  refine ⟨E, X, B, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom a, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom b, ?_⟩
  rw [strictDiagram_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom]
  apply horn₂₂.isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
    exact SSet.yonedaEquiv.symm_apply_apply _

end SerrePositivity.KST.Spectra.CospanShape
