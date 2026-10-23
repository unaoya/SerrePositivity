module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberDiagramChange

/-!
概要：固定辺に付く錐の族を、始点・終点側の区間写像空間へ移す。
方針：元の coslice fiber の制限と、点の表示を揃える同型・区間模型比較を合成する。
規約：元の錐と固定辺を保持する。使われ方：coCartesian な前合成の写像空間比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {T E : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ E) (y : E _⦋0⦌)

/-- 固定辺に付く錐の族を、元の辺とパラメータの join 上へ展開する。 -/
def edgeCosliceUncurry (a : T ⟶ vertexFiber (sliceUnderProjection e) y) :
    join (Δ[1] : SSet.{u}) T ⟶ E :=
  sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection e) y)

/-- 展開した族の左因子への制限は、元の固定辺に一致する。 -/
lemma edgeCosliceUncurry_inl (a : T ⟶ vertexFiber (sliceUnderProjection e) y) :
    joinInl Δ[1] T ≫ edgeCosliceUncurry e y a = e :=
  sliceUnderUncurry_fixed _

/-- 展開した族の右因子は、元の指定終点に定値である。 -/
lemma edgeCosliceUncurry_inr (a : T ⟶ vertexFiber (sliceUnderProjection e) y) :
    joinInr Δ[1] T ≫ edgeCosliceUncurry e y a = SSet.const y := by
  rw [edgeCosliceUncurry, sliceUnderUncurry_projection, Category.assoc,
    vertexFiberι_comp, SSet.comp_const]

/-- 固定辺の指定端点への制限を、元の端点を持つ区間写像空間へ移す。 -/
def edgeCosliceIntervalMap (j : Fin 2) : vertexFiber (sliceUnderProjection e) y ⟶
    intervalMappingSpace (SSet.yonedaEquiv (stdSimplex.δ j ≫ e)) y :=
  cosliceRestrictionFiberMap e (stdSimplex.δ j) y ≫
    (cosliceFiberDiagramIso (Equiv.symm_apply_apply SSet.yonedaEquiv (stdSimplex.δ j ≫ e)).symm
      y).hom ≫ cosliceFiberToIntervalMappingSpace _ y

/-- 区間へ移した族は、元の join 図式と円筒比較の合成として展開される。 -/
lemma edgeCosliceIntervalMap_uncurry (a : T ⟶ vertexFiber (sliceUnderProjection e) y)
    (j : Fin 2) :
    intervalMappingUncurry (a ≫ edgeCosliceIntervalMap e y j) =
      leftMappingSpacePrism T ≫ joinMap (stdSimplex.δ j) (𝟙 T) ≫
        edgeCosliceUncurry e y a := by
  dsimp only [edgeCosliceIntervalMap]
  rw [← Category.assoc, ← Category.assoc, cosliceFiberToIntervalMappingSpace_uncurry]
  unfold cosliceFiberUncurry
  rw [cosliceFiberDiagramIso_uncurry]
  dsimp only [cosliceRestrictionFiberMap]
  rw [Category.assoc, vertexFiberMap_ι]
  rw [← Category.assoc, sliceUnderUncurry_restrict, sliceUnderUncurry_precomp,
    edgeCosliceUncurry, sliceUnderUncurry_precomp]

/-- 元の固定辺を、その元の両端を指定した二切断の辺として表す。 -/
def edgeCosliceEdge : SSet.Truncated.Edge (X := (truncation 2).obj E)
    (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e))
    (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) where
  edge := SSet.yonedaEquiv e
  src_eq := by
    change E.δ 1 (SSet.yonedaEquiv e) = _
    exact (stdSimplex.yonedaEquiv_δ_comp (n := 0) e _).symm
  tgt_eq := by
    change E.δ 0 (SSet.yonedaEquiv e) = _
    exact (stdSimplex.yonedaEquiv_δ_comp (n := 0) e _).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
