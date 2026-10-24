module
public import SerrePositivity.InfinityCategories.Core.BoundaryOpposite

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：頂点を表す零単体の射の反転は反転した頂点の射。
方針：Yoneda によって零次元の反転を計算する。
規約：頂点は opObjEquiv で移す。使われ方：境界の端点条件。 -/
lemma reverseSimplex_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    reverseSimplex 0 (SSet.yonedaEquiv.symm x) =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
  apply SSet.yonedaEquiv.injective
  rfl


/-- 概要：反転した頂点が終対象なら元の頂点は始対象。
方針：最初の頂点を固定した境界を反転して充填する。
規約：単体集合は任意。使われ方：終対象の充填からの双対への復帰。 -/
lemma isInitialVertex_of_isTerminalVertex_op {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex (X := X.op) (SSet.opObjEquiv.symm x)) : IsInitialVertex x := by
  intro n b hb
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ reverseBoundaryMap (n + 1) b =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
    rw [reverseBoundaryMap_vertex, Fin.rev_last, hb, reverseSimplex_vertex]
  obtain ⟨F, hF⟩ := hx n _ hb'
  exact boundaryFiller_of_reverseBoundaryFiller (n + 1) b F hF


/-- 概要：始対象を反転すると終対象になる。
方針：境界を元の単体集合へ戻して始対象で充填し、充填を反転する。
規約：quasicategory 性は不要。使われ方：相対始対象の双対化。 -/
lemma IsInitialVertex.op_isTerminalVertex {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsInitialVertex x) : IsTerminalVertex (X := X.op) (SSet.opObjEquiv.symm x) := by
  intro n b hb
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let b' := reverseBoundaryMap (n + 1) b ≫ q
  have hb' : boundaryVertex n 0 ≫ b' = SSet.yonedaEquiv.symm x := by
    dsimp [b']
    rw [← Category.assoc, reverseBoundaryMap_vertex, Fin.rev_zero, hb,
      reverseSimplex_vertex, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n b' hb'
  apply boundaryFiller_of_reverseBoundaryFiller (n + 1) b
    (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
  rw [← Category.assoc, hF]
  change (reverseBoundaryMap (n + 1) b ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) ≫
    (SSet.opFunctorCompOpFunctorIso.app X).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]


/-- 概要：始対象性は反転した単体集合の終対象性と同値。
方針：境界充填の反転による両方向を組み合わせる。
規約：任意の単体集合。使われ方：始対象を終対象の定理へ移す。 -/
lemma isInitialVertex_iff_isTerminalVertex_op {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔ IsTerminalVertex (X := X.op) (SSet.opObjEquiv.symm x) :=
  ⟨IsInitialVertex.op_isTerminalVertex, isInitialVertex_of_isTerminalVertex_op⟩


/-- 概要：終対象を反転すると始対象になる。
方針：最後の頂点を固定した境界を元へ戻して充填する。
規約：quasicategory 性は不要。使われ方：零対象の双対化。 -/
lemma IsTerminalVertex.op_isInitialVertex {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) : IsInitialVertex (X := X.op) (SSet.opObjEquiv.symm x) := by
  intro n b hb
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let b' := reverseBoundaryMap (n + 1) b ≫ q
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ b' = SSet.yonedaEquiv.symm x := by
    dsimp [b']
    rw [← Category.assoc, reverseBoundaryMap_vertex, Fin.rev_last, hb,
      reverseSimplex_vertex, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n b' hb'
  apply boundaryFiller_of_reverseBoundaryFiller (n + 1) b
    (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
  rw [← Category.assoc, hF]
  change (reverseBoundaryMap (n + 1) b ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) ≫
    (SSet.opFunctorCompOpFunctorIso.app X).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]


end SerrePositivity.InfinityCategories
