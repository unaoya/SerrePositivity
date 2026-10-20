module
public import SerrePositivity.KST.SConstruction.FamilyCylinderTriangleComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy

/-! # 両端固定の二次元円柱と元の区間境界
概要：全時刻で固定した二端点を、元の区間境界全体上の厳密な固定式へ移す。
方針：境界の実二頂点の余積とその tensor を使い、全二面を同時に判定する。
規約：点ごとの固定でなく、元の全パラメータ・全境界の実写像の等号を証明する。
使われ方：単射源構造射への円柱の相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

/-- 元の区間の零頂点の tensor は、零端面と同じ元の実写像。 -/
lemma familyCylinderVertex_zero (U : SSet.{u}) :
    U ◁ stdSimplex.δ (1 : Fin 2) = fst U (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

/-- 元の区間の一頂点の tensor も、一端面と同じ元の実写像。 -/
lemma familyCylinderVertex_one (U : SSet.{u}) :
    U ◁ stdSimplex.δ (0 : Fin 2) = fst U (Δ[0] : SSet.{u}) ≫ SSet.ι₁ := by
  rw [stdSimplex.δ_zero_eq_const]
  rfl

/-- 両端を全時刻固定する円柱は、元の全区間境界の上で同じ円柱に固定される。 -/
lemma familyCylinder_fixed_boundary {U E : SSet.{u}} {f g : U ⟶ E}
    (H : SSet.Homotopy f g) {q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E}
    (h₀ : (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ q = fst U Δ[1] ≫ f)
    (h₁ : (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ q = fst U Δ[1] ≫ g) :
    ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ q =
      fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫
        (U ◁ (SSet.boundary 1).ι) ≫ H.h := by
  let hc := mapIsColimitOfPreservesOfIsColimit (tensorRight (Δ[1] : SSet.{u}))
    _ _ (boundaryColimit U)
  apply hc.hom_ext
  rintro ⟨j⟩
  cases j
  · change ((U ◁ SSet.boundary.ι (1 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
    rw [← Category.assoc, ← comp_whiskerRight, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      familyCylinderVertex_zero, comp_whiskerRight, Category.assoc, h₀]
    change _ = ((U ◁ SSet.boundary.ι (1 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫
      fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫ H.h
    rw [whiskerRight_fst_assoc, whiskerRight_fst_assoc,
      ← Category.assoc (U ◁ SSet.boundary.ι (1 : Fin 2)) (U ◁ (SSet.boundary 1).ι) H.h,
      ← whiskerLeft_comp, SSet.boundary.ι_ι, familyCylinderVertex_zero, Category.assoc, H.h₀]
  · change ((U ◁ SSet.boundary.ι (0 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
    rw [← Category.assoc, ← comp_whiskerRight, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      familyCylinderVertex_one, comp_whiskerRight, Category.assoc, h₁]
    change _ = ((U ◁ SSet.boundary.ι (0 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫
      fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫ H.h
    rw [whiskerRight_fst_assoc, whiskerRight_fst_assoc,
      ← Category.assoc (U ◁ SSet.boundary.ι (0 : Fin 2)) (U ◁ (SSet.boundary 1).ι) H.h,
      ← whiskerLeft_comp, SSet.boundary.ι_ι, familyCylinderVertex_one, Category.assoc, H.h₁]

end SerrePositivity.KST.SConstruction
