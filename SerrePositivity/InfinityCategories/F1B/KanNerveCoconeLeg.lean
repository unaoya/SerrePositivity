module

public import SerrePositivity.InfinityCategories.F1B.KanCoconeLegReverse
public import SerrePositivity.InfinityCategories.F1B.KanNerveOppositeVertices
public import SerrePositivity.InfinityCategories.F1B.KanSliceDiagramConeMap
public import SerrePositivity.InfinityCategories.F1B.KanNerveConeLeg

/-!
概要：通常の余錐の脚と反対圏の nerve の表示を比較する。
方針：反転した錐の脚の公式と図式同型の射への作用を使う。
規約：元の指定された図式・頂点・脚を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：通常の余錐の反転を反対図式の錐の前後合成で表示する。
方針：反対 nerve の辺と反転した錐の脚を計算する。
規約：同じ宇宙の小さい圏の元の指定図式を扱う。
使われ方：B5 の余錐の古典比較。 -/
lemma kanNerveCocone_reverse_val (c : Cocone F) :
    (kanCoconeReverseCone (kanNerveCoconeEquiv c)).val =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveOppositeIso I).inv ≫
        (kanNerveCone c.op).val ≫ (kanNerveOppositeIso C).hom := by
  have he : kanCoconeReverseCone (kanNerveCoconeEquiv c) =
      (kanNerveOppositeSliceIso (F := F)).hom.app _ (kanNerveCone c.op) := by
    change (kanCoconeReverseConeEquiv (nerveMap F))
      ((kanCoconeReverseConeEquiv (nerveMap F)).symm _) = _
    exact (kanCoconeReverseConeEquiv (nerveMap F)).apply_symm_apply _
  rw [he]
  exact kanSliceDiagramIso_hom_val _ _ _ _ _ _

/-- 概要：通常の余錐の脚は nerve へ移した余錐の混合辺に一致する。
方針：反対 nerve の辺と反転した錐の脚を計算する。
規約：同じ宇宙の小さい圏の元の指定図式を扱う。
使われ方：B5 の余錐の古典比較。 -/
lemma kanNerveCocone_leg (c : Cocone F) (i : I) :
    (kanNerveCoconeEquiv c).val.app (Opposite.op ⦋1⦌) (kanJoinCoconeLegSimplex (nerveVertex i)) =
      ComposableArrows.mk₁ (c.ι.app i) := by
  apply SSet.opObjEquiv.symm.injective
  rw [← kanCoconeReverseCone_leg]
  rw [kanNerveCocone_reverse_val]
  change (kanNerveOppositeIso C).hom.app (Opposite.op ⦋1⦌)
    ((kanNerveCone c.op).val.app (Opposite.op ⦋1⦌)
      ((joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveOppositeIso I).inv).app (Opposite.op ⦋1⦌)
        (kanJoinConeLegSimplex (SSet.opObjEquiv.symm (nerveVertex i))))) = _
  rw [kanJoinConeLegSimplex_natural]
  have hp : (kanNerveOppositeIso I).inv.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (nerveVertex i)) = nerveVertex (op i) := by
    rw [← kanNerveOppositeIso_vertex, ← NatTrans.comp_app_apply, Iso.hom_inv_id]
    rfl
  rw [hp]
  change (kanNerveOppositeIso C).hom.app (Opposite.op ⦋1⦌)
    ((kanNerveCone c.op).val.app (Opposite.op ⦋1⦌) (kanConeLegSimplex (op i))) = _
  rw [kanNerveCone_leg]
  exact kanNerveOppositeIso_edge (c.ι.app i)

end SerrePositivity.InfinityCategories.F1B
