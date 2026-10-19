module

public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeEquiv

/-!
概要：通常の余錐と nerve の余錐を反転によって比較する。
方針：反対圏の nerve の同型と slice の同型を合成する。
規約：図式・余錐・頂点を固定し、同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所余極限と pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：余錐の反転は頂点の反転を与える。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
lemma kanCoconeReverseCone_vertex {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCocone p) :
    (kanCoconeReverseCone d).vertex = SSet.opObjEquiv.symm d.vertex := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (kanSliceUnderOpIso_projection p) (Opposite.op ⦋0⦌)) (SSet.opObjEquiv.symm d)
  exact h
/-- 概要：nerve へ移した余錐は通常の指定頂点を保つ。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
lemma kanNerveCocone_vertex (c : Cocone F) : (kanNerveCoconeEquiv c).vertex = nerveVertex c.pt := by
  apply SSet.opObjEquiv.symm.injective
  rw [← kanCoconeReverseCone_vertex]
  have he : kanCoconeReverseCone (kanNerveCoconeEquiv c) =
      (kanNerveOppositeSliceIso (F := F)).hom.app _ (kanNerveCone c.op) := by
    change (kanCoconeReverseConeEquiv (nerveMap F))
      ((kanCoconeReverseConeEquiv (nerveMap F)).symm _) = _
    exact (kanCoconeReverseConeEquiv (nerveMap F)).apply_symm_apply _
  rw [he]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (kanSliceDiagramIso_projection (kanNerveOppositeIso I) (kanNerveOppositeIso C) _ _
      (kanNerveOppositeIso_natural I F)) (Opposite.op ⦋0⦌)) (kanNerveCone c.op)
  change (sliceOverProjection (SSet.opFunctor.map (nerveMap F))).app _
    ((kanNerveOppositeSliceIso (F := F)).hom.app _ (kanNerveCone c.op)) =
      (kanNerveOppositeIso C).hom.app _ (kanNerveCone c.op).vertex at h
  change (sliceOverProjection (SSet.opFunctor.map (nerveMap F))).app _
    ((kanNerveOppositeSliceIso (F := F)).hom.app _ (kanNerveCone c.op)) = _
  rw [h, kanNerveCone_vertex]
  rfl

/-- 概要：読み戻した通常の余錐の頂点は元の native な頂点を表す。
方針：前向きの頂点公式と余錐の全単射の右逆性を使う。
規約：元の図式と native な指定余錐を保持する。
使われ方：B5 の指定局所余錐の復元。 -/
lemma kanNerveCoconeEquiv_symm_vertex (c : JoinCocone (nerveMap F)) :
    nerveVertex ((kanNerveCoconeEquiv (F := F)).symm c).pt = c.vertex := by
  have h := kanNerveCocone_vertex ((kanNerveCoconeEquiv (F := F)).symm c)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F1B
