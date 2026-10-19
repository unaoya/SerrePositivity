module
public import SerrePositivity.KST.SConstruction.ThreeSquareSpanHorns
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # 外側の指定三角形を保つ三正方形の貼り合わせ
概要：三つの外側ホーンに三角形を同時に付け、元の全正方形・全三角形を回収する。
方針：有限余積と pushout の普遍性で、指定した各セルの写像を貼る。
規約：Kan 充填を選び直さず、入力の三角形全体を厳密に保持する。
使われ方：元の K 合成 prism と元の三つの適合区間の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 三つの外側ホーンを元の三正方形へ貼る射。 -/
def threeSquareAllHorns : (∐ fun _ : Fin 3 => (Λ[2, 0] : SSet.{u})) ⟶
    threeSquarePasting := Limits.Sigma.desc threeSquareSpanHorn

/-- 三つのホーンの、対応する三角形への同時包含。 -/
def threeSquareAllHornInclusions : (∐ fun _ : Fin 3 => (Λ[2, 0] : SSet.{u})) ⟶
    ∐ fun _ : Fin 3 => (Δ[2] : SSet.{u}) :=
  Limits.Sigma.map (fun _ : Fin 3 => (horn 2 (0 : Fin 3)).ι)

/-- 元の三正方形に三つの外側三角形を付けた複体。 -/
def threeSquareTrianglePasting : SSet.{u} :=
  pushout (threeSquareAllHorns.{u}) (threeSquareAllHornInclusions.{u})

/-- 貼り合わせ複体への、元の各正方形全体の包含。 -/
def threeSquareTriangleSquare (q : Fin 3) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ threeSquareTrianglePasting :=
  threeSquareInclusion q ≫
    pushout.inl (threeSquareAllHorns.{u}) (threeSquareAllHornInclusions.{u})

/-- 貼り合わせ複体への、指定する各三角形全体の包含。 -/
def threeSquareTriangleCell (e : Fin 3) : (Δ[2] : SSet.{u}) ⟶ threeSquareTrianglePasting :=
  Limits.Sigma.ι (fun _ : Fin 3 => (Δ[2] : SSet.{u})) e ≫
    pushout.inr (threeSquareAllHorns.{u}) (threeSquareAllHornInclusions.{u})

variable {E : SSet.{u}} (q₀ q₁ q₂ : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
  (h₁ : pastingSquareVertical 0 ≫ q₀ = pastingSquareVertical 0 ≫ q₁)
  (h₂ : pastingSquareHorizontal 0 ≫ q₁ = pastingSquareHorizontal 0 ≫ q₂)
  (t : Fin 3 → ((Δ[2] : SSet.{u}) ⟶ E))
  (ht₂ : ∀ e, stdSimplex.δ 2 ≫ t e =
    threeSquareSpanLeft e ≫ threeSquarePastingMap q₀ q₁ q₂ h₁ h₂)
  (ht₁ : ∀ e, stdSimplex.δ 1 ≫ t e =
    threeSquareSpanRight e ≫ threeSquarePastingMap q₀ q₁ q₂ h₁ h₂)

include ht₂ ht₁

/-- 指定三角形の二面の等号から、全ホーン上の厳密な貼り合わせ条件を得る。 -/
lemma threeSquareTrianglePasting_compatible :
    threeSquareAllHorns ≫ threeSquarePastingMap q₀ q₁ q₂ h₁ h₂ =
      threeSquareAllHornInclusions ≫ Limits.Sigma.desc t := by
  apply Limits.Sigma.hom_ext
  intro e
  simp only [threeSquareAllHorns, threeSquareAllHornInclusions,
    Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc]
  apply horn₂₀.isPushout.hom_ext
  · simpa only [← Category.assoc, threeSquareSpanHorn_left, horn.ι_ι] using
      (ht₂ e).symm
  · simpa only [← Category.assoc, threeSquareSpanHorn_right, horn.ι_ι] using
      (ht₁ e).symm

/-- 元の全正方形と指定した全三角形を保つ、複体全体の実写像。 -/
def threeSquareTrianglePastingMap : threeSquareTrianglePasting ⟶ E :=
  pushout.desc (f := threeSquareAllHorns.{u}) (g := threeSquareAllHornInclusions.{u})
    (threeSquarePastingMap q₀ q₁ q₂ h₁ h₂) (Limits.Sigma.desc t)
    (threeSquareTrianglePasting_compatible q₀ q₁ q₂ h₁ h₂ t ht₂ ht₁)

/-- 元の各正方形を全体として厳密に回収する。 -/
lemma threeSquareTrianglePastingMap_square (q : Fin 3) :
    threeSquareTriangleSquare q ≫
      threeSquareTrianglePastingMap q₀ q₁ q₂ h₁ h₂ t ht₂ ht₁ = ![q₀, q₁, q₂] q := by
  simp only [threeSquareTriangleSquare, threeSquareTrianglePastingMap,
    Category.assoc, pushout.inl_desc, threeSquarePastingMap_inclusion]

/-- 指定した各三角形も全体として厳密に回収する。 -/
lemma threeSquareTrianglePastingMap_triangle (e : Fin 3) :
    threeSquareTriangleCell e ≫
      threeSquareTrianglePastingMap q₀ q₁ q₂ h₁ h₂ t ht₂ ht₁ = t e := by
  simp only [threeSquareTriangleCell, threeSquareTrianglePastingMap,
    Category.assoc, pushout.inr_desc, Limits.Sigma.ι_comp_desc]

end SerrePositivity.KST.SConstruction
