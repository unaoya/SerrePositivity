module

public import SerrePositivity.InfinityCategories.F2.Ind.FullSlicePullback
public import SerrePositivity.InfinityCategories.F2.Ind.IndVertexDensity
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes

/-!
概要：Indκ 内の元の Yoneda の左 Kan 局所添字を、前層内の同じ添字へ移す。
方針：全部分圏の slice 引き戻しの同型を、同じ Indκ 頂点と同じ Yoneda に適用する。
規約：元の C への射影を厳密に保持する。
使われ方：証明済みの元の小さい元の圏と Yoneda comma の同値を Indκ へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 引き戻す射の等式による同型は、元の第一射影を保つ。 -/
lemma pullbackCongrHom_projection {A B X : SSet.{u}} {f f' : A ⟶ X} {g g' : B ⟶ X}
    (hf : f = f') (hg : g = g') :
    (pullback.congrHom hf hg).hom ≫ pullback.fst f' g' = pullback.fst f g := by
  cases hf
  cases hg
  simp only [pullback.congrHom, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

/-- 固定図式の表示を等式で移しても、slice 引き戻しの可変始域への射影は変わらない。 -/
lemma slicePullbackTransport_projection {A K X : SSet.{u}} (δ : A ⟶ X)
    {D D' : K ⟶ X} (h : D = D') :
    eqToHom (congrArg (fun d => pullback δ (sliceOverProjection d)) h) ≫
      pullback.fst δ (sliceOverProjection D') = pullback.fst δ (sliceOverProjection D) := by
  subst D'
  rfl

variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌)

/-- 元の Indκ 頂点を表す一点図式は、包含後も同じ前層頂点を表す。 -/
lemma indVertexPoint_inclusion :
    SSet.yonedaEquiv.symm v ≫ indInclusionPresheaf κ C = SSet.yonedaEquiv.symm v.val := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- Indκ 内の同じ左 Kan 局所添字は、周囲の前層内の同じ頂点の添字と厳密に同型。 -/
def indLeftKanShapeAmbientIso :
    leftKanShape (indYoneda κ C) v ≅
      leftKanShape (yonedaInfinityMap C) v.val :=
  fullSlicePullbackIso (IsIndVertex κ C) (indYoneda κ C) (SSet.yonedaEquiv.symm v) ≪≫
    pullback.congrHom (indYoneda_inclusion κ C) rfl ≪≫
    eqToIso (congrArg (fun d => pullback (yonedaInfinityMap C) (sliceOverProjection d))
      (indVertexPoint_inclusion κ v))

/-- 同じ局所添字の同型は元の C の宇宙持ち上げへの射影を厳密に保つ。 -/
lemma indLeftKanShapeAmbientIso_hom_projection :
    (indLeftKanShapeAmbientIso κ v).hom ≫ leftKanProjection (yonedaInfinityMap C) v.val =
      leftKanProjection (indYoneda κ C) v := by
  simp only [indLeftKanShapeAmbientIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    leftKanProjection]
  rw [slicePullbackTransport_projection (yonedaInfinityMap C) (indVertexPoint_inclusion κ v)]
  have hh := pullbackCongrHom_projection
    (g := sliceOverProjection (SSet.yonedaEquiv.symm v ≫ indInclusionPresheaf κ C))
    (g' := sliceOverProjection (SSet.yonedaEquiv.symm v ≫ indInclusionPresheaf κ C))
    (indYoneda_inclusion κ C) rfl
  exact (congrArg (fun f => (fullSlicePullbackIso (IsIndVertex κ C) (indYoneda κ C)
    (SSet.yonedaEquiv.symm v)).hom ≫ f) hh).trans
      (fullSlicePullbackIso_hom_fst (IsIndVertex κ C) (indYoneda κ C) (SSet.yonedaEquiv.symm v))

end SerrePositivity.InfinityCategories.F2.Ind
