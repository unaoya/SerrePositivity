module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-! # 入力境界と比較時刻の両端を同時に固定する全円柱境界
概要：入力の全境界円柱と比較時刻の両端を、その交わりで貼った単射を構成する。
方針：既存の境界 pushout-product を使い、両部分への制限による等号判定を公開する。
規約：二つの境界を同時に扱い、比較時刻の両端固定から入力境界固定を推論しない。
使われ方：全 raw 段比較を全端点固定で逐次厳密化するパラメータ境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open CategoryTheory.MonoidalCategory.Arrow
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {A U : SSet.{u}} (j : A ⟶ U)

/-- 入力境界上の全円柱と比較時刻の両端を同じ交わりで貼った全境界。 -/
def fullCylinderBoundary : SSet.{u} := (KanRelativeLifting.boundaryProduct j).pt

/-- 比較時刻の両端の包含。 -/
def fullCylinderBoundaryTime : U ⊗ (∂Δ[1] : SSet.{u}) ⟶ fullCylinderBoundary j :=
  (KanRelativeLifting.boundaryProduct j).inl

/-- 入力境界上の全円柱の包含。 -/
def fullCylinderBoundaryInput : A ⊗ (Δ[1] : SSet.{u}) ⟶ fullCylinderBoundary j :=
  (KanRelativeLifting.boundaryProduct j).inr

/-- 全円柱境界から元の同じ円柱への包含。 -/
def fullCylinderBoundaryInclusion : fullCylinderBoundary j ⟶ U ⊗ (Δ[1] : SSet.{u}) :=
  (KanRelativeLifting.boundaryProduct j).ι

/-- 入力境界が単射なら、二つの全境界の和も単射。 -/
instance fullCylinderBoundaryInclusion_mono [Mono j] :
    Mono (fullCylinderBoundaryInclusion j) := by
  have : Mono (Arrow.mk j).hom := inferInstanceAs (Mono j)
  have : Mono (Arrow.mk (SSet.boundary.{u} 1).ι).hom :=
    inferInstanceAs (Mono (SSet.boundary.{u} 1).ι)
  exact PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
    (X := Arrow.mk j) (Y := Arrow.mk (SSet.boundary.{u} 1).ι)

/-- 時刻境界は元の同じ両端包含。 -/
lemma fullCylinderBoundaryInclusion_time :
    fullCylinderBoundaryTime j ≫ fullCylinderBoundaryInclusion j =
      U ◁ (SSet.boundary 1).ι := (KanRelativeLifting.boundaryProduct j).inl_ι

/-- 入力境界は元の同じ全境界円柱の包含。 -/
lemma fullCylinderBoundaryInclusion_input :
    fullCylinderBoundaryInput j ≫ fullCylinderBoundaryInclusion j =
      j ▷ (Δ[1] : SSet.{u}) := (KanRelativeLifting.boundaryProduct j).inr_ι

/-- 全境界での等号は、時刻の両端と入力の全境界上の等号で厳密に判定できる。 -/
lemma fullCylinderBoundary_map_iff {E : SSet.{u}} (f g : U ⊗ (Δ[1] : SSet.{u}) ⟶ E) :
    fullCylinderBoundaryInclusion j ≫ f = fullCylinderBoundaryInclusion j ≫ g ↔
      (U ◁ (SSet.boundary 1).ι) ≫ f = (U ◁ (SSet.boundary 1).ι) ≫ g ∧
        (j ▷ (Δ[1] : SSet.{u})) ≫ f = (j ▷ (Δ[1] : SSet.{u})) ≫ g := by
  constructor
  · intro h
    constructor
    · simpa only [← Category.assoc, fullCylinderBoundaryInclusion_time] using
        congrArg (fullCylinderBoundaryTime j ≫ ·) h
    · simpa only [← Category.assoc, fullCylinderBoundaryInclusion_input] using
        congrArg (fullCylinderBoundaryInput j ≫ ·) h
  · rintro ⟨ht, hi⟩
    apply (KanRelativeLifting.boundaryProduct j).isPushout.hom_ext
    · change fullCylinderBoundaryTime j ≫ fullCylinderBoundaryInclusion j ≫ f =
        fullCylinderBoundaryTime j ≫ fullCylinderBoundaryInclusion j ≫ g
      rw [← Category.assoc, fullCylinderBoundaryInclusion_time,
        ← Category.assoc, fullCylinderBoundaryInclusion_time]
      exact ht
    · change fullCylinderBoundaryInput j ≫ fullCylinderBoundaryInclusion j ≫ f =
        fullCylinderBoundaryInput j ≫ fullCylinderBoundaryInclusion j ≫ g
      rw [← Category.assoc, fullCylinderBoundaryInclusion_input,
        ← Category.assoc, fullCylinderBoundaryInclusion_input]
      exact hi

end SerrePositivity.KST.SConstruction
