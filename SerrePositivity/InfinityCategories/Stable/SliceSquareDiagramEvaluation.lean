module
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagram
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-! # Slice の四角形表示と始点評価

概要：錐から四角形への図式表示は始点で元の slice 射影に一致する。
方針：普遍錐の左包含を評価し、cospan の錐と正方形の形状同型で移す。
規約：値域の quasicategory 性は不要。使われ方：D7 の始点の前合成の成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 普遍錐を錐頂点へ制限すると slice 射影になる。 -/
lemma sliceConeFamilyUncurry_inl {K X : SSet.{u}} (p : K ⟶ X) :
    (joinInl (Δ[0] : SSet.{u}) K ▷ sliceOver p) ≫ sliceConeFamilyUncurry p =
      snd Δ[0] (sliceOver p) ≫ sliceOverProjection p := by
  let S := sliceOver p
  have hswap : (joinInl Δ[0] K ▷ S) ≫ (β_ (join (Δ[0] : SSet.{u}) K) S).hom =
      (β_ Δ[0] S).hom ≫ (S ◁ joinInl Δ[0] K) := rfl
  unfold sliceConeFamilyUncurry
  rw [← Category.assoc (joinInl Δ[0] K ▷ S), hswap]
  simp only [Category.assoc]
  rw [← Category.assoc (S ◁ joinInl Δ[0] K), joinTensorLeft_inl]
  rw [← Category.assoc (joinInl (S ⊗ Δ[0]) K), joinInl_joinMap,
    Category.assoc, sliceOverUncurry_projection]
  rfl

/-- 全錐図式の錐頂点での評価は slice 射影。 -/
lemma sliceConeDiagramMap_vertexEvaluation {K X : SSet.{u}} (p : K ⟶ X) :
    sliceConeDiagramMap p ≫ evaluateFunctorAt (Y := X)
      ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) =
      sliceOverProjection p := by
  rw [← stable_pre_evaluateFunctorAt (joinInl (Δ[0] : SSet.{u}) K)]
  rw [← Category.assoc]
  have h : sliceConeDiagramMap p ≫ (pre (joinInl (Δ[0] : SSet.{u}) K)).app X =
      curry (snd Δ[0] (sliceOver p) ≫ sliceOverProjection p) := by
    apply uncurry_injective
    change uncurry (curry (sliceConeFamilyUncurry p) ≫ _) = _
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, sliceConeFamilyUncurry_inl]
  rw [h, curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_snd, Category.id_comp]

/-- 錐の形状同型は左包含を正方形の始点へ送る。 -/
lemma cospanConeSquareIso_initialPoint :
    joinInl (Δ[0] : SSet.{u}) (horn 2 2) ≫ cospanConeSquareIso.hom =
      SSet.yonedaEquiv.symm (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) := by
  have hL := cospanConeSquareIso_left.{u}
  change (joinStdSimplexIso 0 1).inv ≫
    (joinMap (𝟙 (Δ[0] : SSet.{u})) horn₂₂.ι₀₂ ≫ cospanConeSquareIso.hom) =
      squareTriangle 1 at hL
  have hh := congrArg (fun q => (joinStdSimplexIso 0 1).hom ≫ q) hL
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hh
  calc
    _ = joinInl Δ[0] Δ[1] ≫
        (joinMap (𝟙 (Δ[0] : SSet.{u})) horn₂₂.ι₀₂ ≫ cospanConeSquareIso.hom) := by
      rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
    _ = _ := by
      rw [hh, ← Category.assoc, joinStdSimplexIso_inl_vertex]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

/-- 正方形の始点を錐の形状へ戻すと錐頂点になる。 -/
lemma cospanConeSquareIso_inv_initialVertex :
    cospanConeSquareIso.inv.app (Opposite.op ⦋0⦌)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) =
      (joinInl (Δ[0] : SSet.{u}) (horn 2 2)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm 0) := by
  have h := congrArg (fun q => q ≫ cospanConeSquareIso.inv) cospanConeSquareIso_initialPoint.{u}
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  have hh := congrArg (SSet.yonedaEquiv (X := join (Δ[0] : SSet.{u}) (horn 2 2))) h
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hh
  have hv : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have ha := ((stdSimplex.obj₀Equiv.symm (0 : Fin 1)) i).isLt
    have hb := ((SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) i).isLt
    omega
  rw [hv, ← SSet.yonedaEquiv_comp, Category.id_comp]
  exact hh.symm

/-- Slice の四角形表示の始点評価は元の射影。 -/
lemma sliceSquareDiagramMap_sourceEvaluation {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    sliceSquareDiagramMap p ≫ evaluateFunctorAt (Y := X)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) = sliceOverProjection p := by
  rw [sliceSquareDiagramMap, Category.assoc, stable_pre_evaluateFunctorAt,
    cospanConeSquareIso_inv_initialVertex, sliceConeDiagramMap_vertexEvaluation]

end SerrePositivity.InfinityCategories
