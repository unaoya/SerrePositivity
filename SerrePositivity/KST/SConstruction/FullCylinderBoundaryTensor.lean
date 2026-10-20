module
public import SerrePositivity.KST.SConstruction.FullCylinderBoundary

/-! # 全円柱境界と任意の全高次パラメータの等号判定
概要：入力境界と時刻境界の和を、全高次パラメータを保ったまま判定する。
方針：元の境界 pushout をパラメータとの直積へ写し、両脚で等号を判定する。
規約：両全境界を同時に保ち、全パラメータ上の厳密な等号を使う。
使われ方：始辺消去の出力円柱の高次比較で、両全境界を全時刻固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {A U K E : SSet.{u}} (j : A ⟶ U)

/-- 全パラメータを持つ全円柱境界の等号を、元の二つの全境界で判定する。 -/
lemma fullCylinderBoundaryTensorHomExt {f g : fullCylinderBoundary j ⊗ K ⟶ E}
    (ht : (fullCylinderBoundaryTime j ▷ K) ≫ f =
      (fullCylinderBoundaryTime j ▷ K) ≫ g)
    (hi : (fullCylinderBoundaryInput j ▷ K) ≫ f =
      (fullCylinderBoundaryInput j ▷ K) ≫ g) : f = g :=
  ((KanRelativeLifting.boundaryProduct j).isPushout.map (tensorRight K)).hom_ext ht hi

/-- 全円柱境界の全パラメータ固定を、時刻境界と入力境界で厳密に判定する。 -/
lemma fullCylinderBoundaryTensor_fixed_iff (f : U ⊗ (Δ[1] : SSet.{u}) ⟶ E)
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ K ⟶ E) :
    (fullCylinderBoundaryInclusion j ▷ K) ≫ q =
      fst (fullCylinderBoundary j) K ≫ fullCylinderBoundaryInclusion j ≫ f ↔
    ((U ◁ (SSet.boundary 1).ι) ▷ K) ≫ q =
      fst (U ⊗ (∂Δ[1] : SSet.{u})) K ≫ (U ◁ (SSet.boundary 1).ι) ≫ f ∧
    ((j ▷ (Δ[1] : SSet.{u})) ▷ K) ≫ q =
      fst (A ⊗ (Δ[1] : SSet.{u})) K ≫ (j ▷ (Δ[1] : SSet.{u})) ≫ f := by
  constructor
  · intro h
    constructor
    · have ht := congrArg ((fullCylinderBoundaryTime j ▷ K) ≫ ·) h
      rw [← Category.assoc, ← comp_whiskerRight, fullCylinderBoundaryInclusion_time,
        whiskerRight_fst_assoc, ← Category.assoc (fullCylinderBoundaryTime j),
        fullCylinderBoundaryInclusion_time] at ht
      exact ht
    · have hi := congrArg ((fullCylinderBoundaryInput j ▷ K) ≫ ·) h
      rw [← Category.assoc, ← comp_whiskerRight, fullCylinderBoundaryInclusion_input,
        whiskerRight_fst_assoc, ← Category.assoc (fullCylinderBoundaryInput j),
        fullCylinderBoundaryInclusion_input] at hi
      exact hi
  · rintro ⟨ht, hi⟩
    apply fullCylinderBoundaryTensorHomExt j
    · rw [← Category.assoc, ← comp_whiskerRight, fullCylinderBoundaryInclusion_time,
        whiskerRight_fst_assoc, ← Category.assoc (fullCylinderBoundaryTime j),
        fullCylinderBoundaryInclusion_time]
      exact ht
    · rw [← Category.assoc, ← comp_whiskerRight, fullCylinderBoundaryInclusion_input,
        whiskerRight_fst_assoc, ← Category.assoc (fullCylinderBoundaryInput j),
        fullCylinderBoundaryInclusion_input]
      exact hi

end SerrePositivity.KST.SConstruction
