module

public import SerrePositivity.InfinityCategories.F2.Presentable.SplitCoconeExtensionFaces
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero

/-!
概要：分裂三角形から挿入される標的頂点の全増大辺は恒等辺。
方針：反復 coslice の全右面と恒等長辺を射影して計算する。
規約：全二点 join からの射の厳密な等式。
使われ方：交互可算図式の奇数部分列を固定標的の定値図式と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {K C : SSet.{u}} {F : K ⟶ C} {c d : (sliceUnder F) _⦋0⦌}
  {e : (sliceUnder F).Edge c d} {r : (sliceUnder F).Edge d c}

private lemma identityEdgeCocone_val {X : SSet.{u}} (x : X _⦋0⦌) :
    (edgeCosliceVertex (SSet.Edge.id x).toTruncated).val =
      (SSet.const x : join (Δ[0] : SSet.{u}) Δ[0] ⟶ X) := by
  change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (SSet.Edge.id x).edge = _
  have h : (SSet.Edge.id x).edge = PinchedHom.constant x 1 := (pinchedConstant_one x).symm
  have hy : SSet.yonedaEquiv.symm (PinchedHom.constant x 1) =
      (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [h, hy, SSet.comp_const]

/-- 概要：最初の挿入頂点から元の標的への全辺は厳密な恒等辺。
方針：三角形余錐の始点面を元の圏へ射影する。
規約：元の増大余錐頂点を保持する全射の等式。
使われ方：奇数部分列の各頂点の終対象性。 -/
lemma splitCoconeExtension_inserted_identity (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (SSet.stdSimplex.δ (1 : Fin 2) ≫ joinInr K Δ[1]) (𝟙 Δ[0]) ≫
      (splitCoconeExtension T).val =
        SSet.const ((sliceUnderProjection F).app (Opposite.op ⦋0⦌) c) := by
  rw [← Category.comp_id (𝟙 (Δ[0] : SSet.{u})), joinMap_comp, Category.assoc,
    splitCoconeExtension, iteratedCocone_vertex_val,
    ← Category.assoc (joinMap (joinInr K Δ[1]) _), joinAssociator_rightPair,
    sliceUnderUncurry_projection, ← Category.assoc]
  have h := compStructCocone_source_val T
  change joinMap (SSet.stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
    (compStructCocone T).val = (edgeCosliceVertex (SSet.Edge.id c).toTruncated).val at h
  rw [h, identityEdgeCocone_val, SSet.const_comp]

end SerrePositivity.InfinityCategories.F2.Presentable
