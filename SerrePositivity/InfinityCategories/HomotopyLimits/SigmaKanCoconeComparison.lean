module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaElementsLeftKanModel
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaVertexDensity
public import SerrePositivity.InfinityCategories.F2.Ind.IndDensityKanCoconeMap

/-!
概要：元の P_Σ の局所 Kan 全余錐を、同じ元の小さい元の圏の全密度余錐へ同定。
方針：全部分圏・頂点表示・comma 因子交換の厳密な同型を、全余錐の射で追跡する。
規約：元の指定頂点と全単体を保持。使われ方：sifted 保存関手の標準左 Kan 条件。
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

/-- 同じ局所添字の同型は、普遍余錐全体を元の全部分包含による後合成へ写す。 -/
lemma sigmaLeftKanShapeAmbientIso_coconeMap :
    joinMap (sigmaLeftKanShapeAmbientIso v).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      slicePullbackCoconeMap (yonedaInfinityMap C) (SSet.yonedaEquiv.symm v.val) =
    slicePullbackCoconeMap (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v) ≫
      sigmaPresheafInfinityInclusion C := by
  simp only [sigmaLeftKanShapeAmbientIso, Iso.trans_hom, eqToIso.hom,
    joinMap_comp_fixed, Category.assoc]
  have ht := slicePullbackCoconeMap_transport (yonedaInfinityMap C) (sigmaVertexPoint_inclusion v)
  have hd := slicePullbackCoconeMap_congrHom (sigmaYonedaInfinityMap_inclusion C)
    (SSet.yonedaEquiv.symm v ≫ sigmaPresheafInfinityInclusion C)
  have h₁ := congrArg (fun f =>
    joinMap (fullSlicePullbackIso (IsSigmaPresheaf (C := C)) (sigmaYonedaInfinityMap C)
      (SSet.yonedaEquiv.symm v)).hom (𝟙 Δ[0]) ≫
    joinMap (pullback.congrHom (sigmaYonedaInfinityMap_inclusion C)
      (rfl : sliceOverProjection (SSet.yonedaEquiv.symm v ≫ sigmaPresheafInfinityInclusion C) =
        sliceOverProjection (SSet.yonedaEquiv.symm v ≫ sigmaPresheafInfinityInclusion C))).hom
      (𝟙 Δ[0]) ≫ f) ht
  have h₂ := congrArg (fun f =>
    joinMap (fullSlicePullbackIso (IsSigmaPresheaf (C := C)) (sigmaYonedaInfinityMap C)
      (SSet.yonedaEquiv.symm v)).hom (𝟙 Δ[0]) ≫ f) hd
  exact h₁.trans (h₂.trans (fullSlicePullbackIso_hom_coconeMap
    (IsSigmaPresheaf (C := C)) (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v)))

/-- 同じ comma 同型は、全普遍余錐を元の前層の同じ余錐へ写す。 -/
lemma sigmaLeftKanCommaIso_hom_coconeMap :
    joinMap (sigmaLeftKanCommaIso v).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (presheafYonedaSliceCocone (sigmaPresheafVertexFunctor v)).val =
    slicePullbackCoconeMap (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v) ≫
      sigmaPresheafInfinityInclusion C := by
  simp only [sigmaLeftKanCommaIso, Iso.trans_hom, eqToIso.hom,
    joinMap_comp_fixed, Category.assoc]
  have hs := pullbackSymmetry_coconeMap (yonedaInfinityMap C)
    (SSet.yonedaEquiv.symm (functorVertex (sigmaPresheafVertexFunctor v)))
  have ht := leftKanShapeTransport_coconeMap (yonedaInfinityMap C)
    (sigmaPresheafVertexFunctor_vertex v).symm
  have h₁ := congrArg (fun f => joinMap (sigmaLeftKanShapeAmbientIso v).hom (𝟙 Δ[0]) ≫
    joinMap (eqToHom (congrArg (leftKanShape (yonedaInfinityMap C))
      (sigmaPresheafVertexFunctor_vertex v).symm)) (𝟙 Δ[0]) ≫ f) hs
  have h₂ := congrArg (fun f => joinMap (sigmaLeftKanShapeAmbientIso v).hom (𝟙 Δ[0]) ≫ f) ht
  exact h₁.trans (h₂.trans (sigmaLeftKanShapeAmbientIso_coconeMap v))

/-- 同じ逆同型で戻した局所 Kan 余錐は、元の Yoneda comma の余錐そのもの。 -/
lemma sigmaLeftKanCommaIso_inv_coconeMap :
    joinMap (sigmaLeftKanCommaIso v).inv (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      slicePullbackCoconeMap (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v) ≫
      sigmaPresheafInfinityInclusion C =
        (presheafYonedaSliceCocone (sigmaPresheafVertexFunctor v)).val := by
  calc
    _ = joinMap (sigmaLeftKanCommaIso v).inv (𝟙 Δ[0]) ≫
        (joinMap (sigmaLeftKanCommaIso v).hom (𝟙 Δ[0]) ≫
          (presheafYonedaSliceCocone (sigmaPresheafVertexFunctor v)).val) :=
      congrArg (fun f => joinMap (sigmaLeftKanCommaIso v).inv (𝟙 Δ[0]) ≫ f)
        (sigmaLeftKanCommaIso_hom_coconeMap v).symm
    _ = _ := by
      rw [← Category.assoc, ← joinMap_comp, Iso.inv_hom_id,
        Category.id_comp, joinMap_id, Category.id_comp]

/-- 元の指定 P_Σ 密度余錐を周囲へ含めると、同じ前層の全密度余錐そのもの。 -/
lemma sigmaVertexDensityCocone_val_inclusion :
    (sigmaVertexDensityCocone v).val ≫ sigmaPresheafInfinityInclusion C =
      (presheafDensityCocone (sigmaPresheafVertexFunctor v)).val := by
  have h := congrArg Subtype.val (sigmaDensityCocone_inclusion (sigmaPresheafVertexFunctor v)
    (sigmaVertexPresheaf_mem v))
  exact h

/-- 小さい元の圏へ制限した同じ標準 Kan 余錐の全射は、元の P_Σ 密度余錐そのもの。 -/
lemma sigmaElementsLeftKanComparison_coconeMap :
    joinMap (sigmaElementsLeftKanComparison v) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      slicePullbackCoconeMap (sigmaYonedaInfinityMap C) (SSet.yonedaEquiv.symm v) =
        (sigmaVertexDensityCocone v).val := by
  have : Mono (sigmaPresheafInfinityInclusion C) := inferInstanceAs
    (Mono (fullSubcomplexOnVertices (PresheafInfinity C) (IsSigmaPresheaf (C := C))).ι)
  apply (cancel_mono (sigmaPresheafInfinityInclusion C)).mp
  simp only [sigmaElementsLeftKanComparison, joinMap_comp_fixed, Category.assoc]
  have h := congrArg (fun f =>
    joinMap (presheafElementsYonedaSliceComparison (sigmaPresheafVertexFunctor v)) (𝟙 Δ[0]) ≫ f)
      (sigmaLeftKanCommaIso_inv_coconeMap v)
  exact h.trans ((presheafElementsYonedaSliceComparison_coconeMap
    (sigmaPresheafVertexFunctor v)).trans (sigmaVertexDensityCocone_val_inclusion v).symm)

end SerrePositivity.InfinityCategories.HomotopyLimits
