module

public import SerrePositivity.InfinityCategories.F2.Ind.IndAmbientCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanCommaIso

/-!
概要：Indκ の局所 Kan 添字と元の Yoneda comma の同じ普遍余錐を比較する。
方針：元の頂点表示の移送と、引き戻しの因子交換を全錐の射で追跡する。
規約：元の C・指定 Indκ 頂点・同じ前層の全余錐を保持する。
使われ方：同じ小さい元の圏への制限を密度余錐へ同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の頂点の表示変更でも、局所 Kan 添字の全普遍余錐は変わらない。 -/
lemma leftKanShapeTransport_coconeMap {K X : SSet.{u}} (δ : K ⟶ X)
    {v w : X _⦋0⦌} (h : v = w) :
    joinMap (eqToHom (congrArg (leftKanShape δ) h)) (𝟙 (Δ[0] : SSet.{u})) ≫
      slicePullbackCoconeMap δ (SSet.yonedaEquiv.symm w) =
        slicePullbackCoconeMap δ (SSet.yonedaEquiv.symm v) := by
  subst w
  rw [eqToHom_refl, joinMap_id, Category.id_comp]

/-- 引き戻しの因子を交換しても、同じ slice の全普遍錐を回収する。 -/
lemma pullbackSymmetry_coconeMap {A K X : SSet.{u}} (δ : A ⟶ X) (D : K ⟶ X) :
    joinMap (pullbackSymmetry δ (sliceOverProjection D)).hom (𝟙 K) ≫
      sliceOverUncurry (pullback.fst (sliceOverProjection D) δ) =
        slicePullbackCoconeMap δ D := by
  rw [← sliceOverUncurry_precomp, pullbackSymmetry_hom_comp_fst]
  rfl

variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌)

/-- 同じ comma 同型は、全普遍余錐を元の前層の同じ余錐へ写す。 -/
lemma indLeftKanCommaIso_hom_coconeMap :
    joinMap (indLeftKanCommaIso κ v).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (presheafYonedaSliceCocone (indVertexPresheaf κ v)).val =
    slicePullbackCoconeMap (indYoneda κ C) (SSet.yonedaEquiv.symm v) ≫
      indInclusionPresheaf κ C := by
  simp only [indLeftKanCommaIso, Iso.trans_hom, eqToIso.hom,
    joinMap_comp_fixed, Category.assoc]
  have hs := pullbackSymmetry_coconeMap (yonedaInfinityMap C)
    (SSet.yonedaEquiv.symm (functorVertex (indVertexPresheaf κ v)))
  have ht := leftKanShapeTransport_coconeMap (yonedaInfinityMap C)
    (indVertexPresheaf_vertex κ v).symm
  have h₁ := congrArg (fun f => joinMap (indLeftKanShapeAmbientIso κ v).hom (𝟙 Δ[0]) ≫
    joinMap (eqToHom (congrArg (leftKanShape (yonedaInfinityMap C))
      (indVertexPresheaf_vertex κ v).symm)) (𝟙 Δ[0]) ≫ f) hs
  have h₂ := congrArg (fun f => joinMap (indLeftKanShapeAmbientIso κ v).hom (𝟙 Δ[0]) ≫ f) ht
  exact h₁.trans (h₂.trans (indLeftKanShapeAmbientIso_coconeMap κ v))

/-- 同じ逆同型で戻した局所 Kan 余錐は、元の Yoneda comma の余錐そのもの。 -/
lemma indLeftKanCommaIso_inv_coconeMap :
    joinMap (indLeftKanCommaIso κ v).inv (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      slicePullbackCoconeMap (indYoneda κ C) (SSet.yonedaEquiv.symm v) ≫
      indInclusionPresheaf κ C = (presheafYonedaSliceCocone (indVertexPresheaf κ v)).val := by
  calc
    _ = joinMap (indLeftKanCommaIso κ v).inv (𝟙 Δ[0]) ≫
        (joinMap (indLeftKanCommaIso κ v).hom (𝟙 Δ[0]) ≫
          (presheafYonedaSliceCocone (indVertexPresheaf κ v)).val) :=
      congrArg (fun f => joinMap (indLeftKanCommaIso κ v).inv (𝟙 Δ[0]) ≫ f)
        (indLeftKanCommaIso_hom_coconeMap κ v).symm
    _ = _ := by
      rw [← Category.assoc, ← joinMap_comp, Iso.inv_hom_id,
        Category.id_comp, joinMap_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Ind
