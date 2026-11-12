module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.BoundaryOpposite

/-! General declarations moved verbatim from their original modules.

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 概要：頂点を表す零単体の射の反転は反転した頂点の射。
方針：Yoneda によって零次元の反転を計算する。
規約：頂点は opObjEquiv で移す。使われ方：境界の端点条件。 -/
lemma reverseSimplex_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 0 (SSet.yonedaEquiv.symm x) =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
  apply SSet.yonedaEquiv.injective
  rfl


/-- 概要：反転した頂点が終対象なら元の頂点は始対象。
方針：最初の頂点を固定した境界を反転して充填する。
規約：単体集合は任意。使われ方：終対象の充填からの双対への復帰。 -/
lemma isInitialVertex_of_isTerminalVertex_op {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := X.op) (SSet.opObjEquiv.symm x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  intro n b hb
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) b =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_vertex, Fin.rev_last, hb, reverseSimplex_vertex]
  obtain ⟨F, hF⟩ := hx n _ hb'
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.boundaryFiller_of_reverseBoundaryFiller (n + 1) b F hF


/-- 概要：始対象を反転すると終対象になる。
方針：境界を元の単体集合へ戻して始対象で充填し、充填を反転する。
規約：quasicategory 性は不要。使われ方：相対始対象の双対化。 -/
lemma IsInitialVertex.op_isTerminalVertex {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := X.op) (SSet.opObjEquiv.symm x) := by
  intro n b hb
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let b' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) b ≫ q
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b' = SSet.yonedaEquiv.symm x := by
    dsimp [b']
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_vertex, Fin.rev_zero, hb,
      reverseSimplex_vertex, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n b' hb'
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.boundaryFiller_of_reverseBoundaryFiller (n + 1) b
    (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
  rw [← Category.assoc, hF]
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) b ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) ≫
    (SSet.opFunctorCompOpFunctorIso.app X).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsInitialVertex (op_isTerminalVertex)



/-- 概要：始対象性は反転した単体集合の終対象性と同値。
方針：境界充填の反転による両方向を組み合わせる。
規約：任意の単体集合。使われ方：始対象を終対象の定理へ移す。 -/
lemma isInitialVertex_iff_isTerminalVertex_op {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := X.op) (SSet.opObjEquiv.symm x) :=
  ⟨IsInitialVertex.op_isTerminalVertex, isInitialVertex_of_isTerminalVertex_op⟩


/-- 概要：終対象を反転すると始対象になる。
方針：最後の頂点を固定した境界を元へ戻して充填する。
規約：quasicategory 性は不要。使われ方：零対象の双対化。 -/
lemma IsTerminalVertex.op_isInitialVertex {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := X.op) (SSet.opObjEquiv.symm x) := by
  intro n b hb
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let b' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) b ≫ q
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b' = SSet.yonedaEquiv.symm x := by
    dsimp [b']
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_vertex, Fin.rev_last, hb,
      reverseSimplex_vertex, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n b' hb'
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.boundaryFiller_of_reverseBoundaryFiller (n + 1) b
    (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
  rw [← Category.assoc, hF]
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) b ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) ≫
    (SSet.opFunctorCompOpFunctorIso.app X).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsTerminalVertex (op_isInitialVertex)



end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
