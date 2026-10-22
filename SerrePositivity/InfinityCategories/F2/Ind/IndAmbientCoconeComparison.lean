module

public import SerrePositivity.InfinityCategories.F2.Ind.SlicePullbackCoconeTransport

/-!
概要：Indκ 内の局所 Kan 普遍余錐を、周囲の前層内の同じ全余錐へ同定する。
方針：全部分圏の引き戻し同型と、二つの図式表示変更の全錐の自然性を合成する。
規約：同じ元の Indκ 頂点を保つ厳密な全余錐の等式。
使われ方：小さい元の圏への制限を元の密度余錐へ同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌)

/-- 同じ局所添字の同型は、普遍余錐全体を元の全部分包含による後合成へ写す。 -/
lemma indLeftKanShapeAmbientIso_coconeMap :
    joinMap (indLeftKanShapeAmbientIso κ v).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      slicePullbackCoconeMap (yonedaInfinityMap C) (SSet.yonedaEquiv.symm v.val) =
    slicePullbackCoconeMap (indYoneda κ C) (SSet.yonedaEquiv.symm v) ≫
      indInclusionPresheaf κ C := by
  simp only [indLeftKanShapeAmbientIso, Iso.trans_hom, eqToIso.hom,
    joinMap_comp_fixed, Category.assoc]
  have ht := slicePullbackCoconeMap_transport (yonedaInfinityMap C) (indVertexPoint_inclusion κ v)
  have hd := slicePullbackCoconeMap_congrHom (indYoneda_inclusion κ C)
    (SSet.yonedaEquiv.symm v ≫ indInclusionPresheaf κ C)
  have h₁ := congrArg (fun f =>
    joinMap (fullSlicePullbackIso (IsIndVertex κ C) (indYoneda κ C)
      (SSet.yonedaEquiv.symm v)).hom (𝟙 Δ[0]) ≫
    joinMap (pullback.congrHom (indYoneda_inclusion κ C)
      (rfl : sliceOverProjection (SSet.yonedaEquiv.symm v ≫ indInclusionPresheaf κ C) =
        sliceOverProjection (SSet.yonedaEquiv.symm v ≫ indInclusionPresheaf κ C))).hom
      (𝟙 Δ[0]) ≫ f) ht
  have h₂ := congrArg (fun f =>
    joinMap (fullSlicePullbackIso (IsIndVertex κ C) (indYoneda κ C)
      (SSet.yonedaEquiv.symm v)).hom (𝟙 Δ[0]) ≫ f) hd
  exact h₁.trans (h₂.trans (fullSlicePullbackIso_hom_coconeMap
    (IsIndVertex κ C) (indYoneda κ C) (SSet.yonedaEquiv.symm v)))

end SerrePositivity.InfinityCategories.F2.Ind
