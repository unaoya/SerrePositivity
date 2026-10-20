module
public import SerrePositivity.KST.SConstruction.FixedBoundaryPostcomposition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # 全境界固定円柱の入口と全側面を同じ境界にする
概要：円柱の入口と入力境界上の全側面を一つの実境界複体へ貼り、元の入力へ折り畳む。
方針：境界円柱と入口を時刻零で pushout し、元の包含と第一射影を降ろす。
規約：全入力境界と全時刻を同時に保持し、端点だけの比較にしない。
使われ方：元の全端点固定正規化円柱を、共有頂点を固定して比較複体へ貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {A U : SSet.{u}} (j : A ⟶ U)

/-- 全側面と入口を、元の時刻零境界で貼った実境界複体。 -/
def fixedCylinderBoundary : SSet.{u} := pushout (SSet.ι₀ (X := A)) j

/-- 入力境界上の元の全円柱側面の包含。 -/
def fixedCylinderBoundaryVertical : A ⊗ (Δ[1] : SSet.{u}) ⟶ fixedCylinderBoundary j :=
  pushout.inl (SSet.ι₀ (X := A)) j

/-- 元の全入口の包含。 -/
def fixedCylinderBoundarySource : U ⟶ fixedCylinderBoundary j :=
  pushout.inr (SSet.ι₀ (X := A)) j

/-- 入口と全側面を、元の同じ全円柱へ写す包含。 -/
def fixedCylinderBoundaryInclusion : fixedCylinderBoundary j ⟶ U ⊗ (Δ[1] : SSet.{u}) :=
  pushout.desc (f := SSet.ι₀ (X := A)) (g := j) (j ▷ (Δ[1] : SSet.{u})) SSet.ι₀
    (SSet.ι₀_comp j)

/-- 入口と全側面を、元の入力の同じ境界へ折り畳む実写像。 -/
def fixedCylinderBoundaryFold : fixedCylinderBoundary j ⟶ U :=
  pushout.desc (f := SSet.ι₀ (X := A)) (g := j) (fst A Δ[1] ≫ j) (𝟙 U)
    (by rw [SSet.ι₀_fst_assoc, Category.comp_id])

/-- 全側面の包含は、元の同じ境界円柱の包含。 -/
lemma fixedCylinderBoundaryInclusion_vertical :
    fixedCylinderBoundaryVertical j ≫ fixedCylinderBoundaryInclusion j = j ▷ (Δ[1] : SSet.{u}) :=
  pushout.inl_desc _ _ _

/-- 全入口の包含は、元の同じ時刻零包含。 -/
lemma fixedCylinderBoundaryInclusion_source :
    fixedCylinderBoundarySource j ≫ fixedCylinderBoundaryInclusion j = SSet.ι₀ :=
  pushout.inr_desc _ _ _

/-- 全側面は、全時刻で元の同じ入力境界へ折り畳まれる。 -/
lemma fixedCylinderBoundaryFold_vertical :
    fixedCylinderBoundaryVertical j ≫ fixedCylinderBoundaryFold j = fst A Δ[1] ≫ j :=
  pushout.inl_desc _ _ _

/-- 全入口は、元の入力そのものへ折り畳まれる。 -/
lemma fixedCylinderBoundaryFold_source :
    fixedCylinderBoundarySource j ≫ fixedCylinderBoundaryFold j = 𝟙 U :=
  pushout.inr_desc _ _ _

variable {E : SSet.{u}} {f g : U ⟶ E} (H : SSet.Homotopy f g)
  (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ j ≫ f)

include hr in
/-- 元の全境界固定式は、入口と全側面の複体全体の厳密な折り畳み式。 -/
lemma fixedCylinderBoundary_map :
    fixedCylinderBoundaryInclusion j ≫ H.h = fixedCylinderBoundaryFold j ≫ f := by
  apply pushout.hom_ext
  · change fixedCylinderBoundaryVertical j ≫ fixedCylinderBoundaryInclusion j ≫ H.h =
      fixedCylinderBoundaryVertical j ≫ fixedCylinderBoundaryFold j ≫ f
    calc
      _ = (j ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
        rw [← Category.assoc, fixedCylinderBoundaryInclusion_vertical]
      _ = fst A Δ[1] ≫ j ≫ f := hr
      _ = _ := by
        simpa only [Category.assoc] using
          (congrArg (· ≫ f) (fixedCylinderBoundaryFold_vertical j)).symm
  · change fixedCylinderBoundarySource j ≫ fixedCylinderBoundaryInclusion j ≫ H.h =
      fixedCylinderBoundarySource j ≫ fixedCylinderBoundaryFold j ≫ f
    rw [← Category.assoc, fixedCylinderBoundaryInclusion_source, H.h₀,
      ← Category.assoc, fixedCylinderBoundaryFold_source, Category.id_comp]

end SerrePositivity.KST.SConstruction
