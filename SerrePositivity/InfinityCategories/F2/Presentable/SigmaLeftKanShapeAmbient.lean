module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaYonedaEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanCommaIso

/-!
概要：元の P_Σ Yoneda の左 Kan 添字を、同じ前層への元の Yoneda comma へ移す。
方針：公開済みの全部分圏の引き戻し同型と、元の前層の厳密な頂点表示を合成する。
規約：元の小さい C の宇宙持ち上げへの射影を全単体で保持する。
使われ方：小さい sifted な元の圏を、P_Σ の左 Kan 局所添字の模型にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C] (v : (SigmaPresheafInfinity C) _⦋0⦌)

omit [Quasicategory C] in
/-- 元の P_Σ 頂点の一点図式は、包含後に同じ前層頂点を表す。 -/
lemma sigmaVertexPoint_inclusion :
    SSet.yonedaEquiv.symm v ≫ sigmaPresheafInfinityInclusion C = SSet.yonedaEquiv.symm v.val := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- P_Σ 内の元の左 Kan 添字と、周囲の同じ前層頂点での左 Kan 添字の厳密な同型。 -/
def sigmaLeftKanShapeAmbientIso : leftKanShape (sigmaYonedaInfinityMap C) v ≅
    leftKanShape (yonedaInfinityMap C) v.val :=
  fullSlicePullbackIso (IsSigmaPresheaf (C := C)) (sigmaYonedaInfinityMap C)
      (SSet.yonedaEquiv.symm v) ≪≫
    pullback.congrHom (sigmaYonedaInfinityMap_inclusion C) rfl ≪≫
    eqToIso (congrArg (fun d => pullback (yonedaInfinityMap C) (sliceOverProjection d))
      (sigmaVertexPoint_inclusion v))

/-- 同じ形状同型は、元の C への射影を厳密に保つ。 -/
lemma sigmaLeftKanShapeAmbientIso_hom_projection :
    (sigmaLeftKanShapeAmbientIso v).hom ≫ leftKanProjection (yonedaInfinityMap C) v.val =
      leftKanProjection (sigmaYonedaInfinityMap C) v := by
  simp only [sigmaLeftKanShapeAmbientIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    leftKanProjection]
  rw [slicePullbackTransport_projection (yonedaInfinityMap C) (sigmaVertexPoint_inclusion v)]
  have hh := pullbackCongrHom_projection
    (g := sliceOverProjection (SSet.yonedaEquiv.symm v ≫ sigmaPresheafInfinityInclusion C))
    (g' := sliceOverProjection (SSet.yonedaEquiv.symm v ≫ sigmaPresheafInfinityInclusion C))
    (sigmaYonedaInfinityMap_inclusion C) rfl
  exact (congrArg (fun f => (fullSlicePullbackIso (IsSigmaPresheaf (C := C))
    (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v)).hom ≫ f) hh).trans
      (fullSlicePullbackIso_hom_fst (IsSigmaPresheaf (C := C)) (sigmaYonedaInfinityMap C)
        (SSet.yonedaEquiv.symm v))

/-- 同じ左 Kan 添字と、元の指定前層の Yoneda comma の厳密な同型。 -/
def sigmaLeftKanCommaIso : leftKanShape (sigmaYonedaInfinityMap C) v ≅
    presheafYonedaSlice (sigmaPresheafVertexFunctor v) :=
  sigmaLeftKanShapeAmbientIso v ≪≫
    eqToIso (congrArg (leftKanShape (yonedaInfinityMap C))
      (sigmaPresheafVertexFunctor_vertex v).symm) ≪≫
    pullbackSymmetry (yonedaInfinityMap C)
      (sliceOverProjection (SSet.yonedaEquiv.symm
        (functorVertex (sigmaPresheafVertexFunctor v))))

/-- 同じ comma 同型は元の C への射影を厳密に保つ。 -/
lemma sigmaLeftKanCommaIso_hom_projection :
    (sigmaLeftKanCommaIso v).hom ≫ presheafYonedaSliceProjection (sigmaPresheafVertexFunctor v) =
      leftKanProjection (sigmaYonedaInfinityMap C) v := by
  simp only [sigmaLeftKanCommaIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    presheafYonedaSliceProjection, pullbackSymmetry_hom_comp_snd]
  have ht := leftKanShapeTransport_projection (yonedaInfinityMap C)
    (sigmaPresheafVertexFunctor_vertex v).symm
  exact (congrArg (fun f => (sigmaLeftKanShapeAmbientIso v).hom ≫ f) ht).trans
    (sigmaLeftKanShapeAmbientIso_hom_projection v)

/-- 同じ逆同型も、元の C への射影を厳密に保つ。 -/
lemma sigmaLeftKanCommaIso_inv_projection :
    (sigmaLeftKanCommaIso v).inv ≫ leftKanProjection (sigmaYonedaInfinityMap C) v =
      presheafYonedaSliceProjection (sigmaPresheafVertexFunctor v) := by
  rw [← sigmaLeftKanCommaIso_hom_projection, (sigmaLeftKanCommaIso v).inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.HomotopyLimits
