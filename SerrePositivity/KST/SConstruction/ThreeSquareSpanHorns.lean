module
public import SerrePositivity.KST.SConstruction.ThreeSquarePasting
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 三正方形の外側三ホーン
概要：貼り合わせた三正方形の六つの外側脚から、三つの指定ホーンを作る。
方針：共有区間の端点を照合し、ホーンの pushout の普遍性を使う。
規約：脚は元の正方形への包含との実合成であり、置き換えない。
使われ方：合成射と前後の射の指定三角形を同時に貼る境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 合成射、前の射、後の射の順の、外側ホーンの第一脚。 -/
def threeSquareSpanLeft (e : Fin 3) : (Δ[1] : SSet.{u}) ⟶ threeSquarePasting :=
  ![pastingSquareHorizontal 0 ≫ threeSquareInclusion.{u} 0,
    pastingSquareHorizontal 1 ≫ threeSquareInclusion.{u} 0,
    pastingSquareVertical 1 ≫ threeSquareInclusion.{u} 1] e

/-- 同じ順の、外側ホーンの第二脚。 -/
def threeSquareSpanRight (e : Fin 3) : (Δ[1] : SSet.{u}) ⟶ threeSquarePasting :=
  ![pastingSquareVertical 0 ≫ threeSquareInclusion.{u} 2,
    pastingSquareHorizontal 1 ≫ threeSquareInclusion.{u} 1,
    pastingSquareVertical 1 ≫ threeSquareInclusion.{u} 2] e

/-- 三つの外側の脚対は、それぞれ元の同じ始点を持つ。 -/
lemma threeSquareSpan_start (e : Fin 3) :
    pastingIntervalVertex 0 ≫ threeSquareSpanLeft.{u} e =
      pastingIntervalVertex 0 ≫ threeSquareSpanRight e := by
  have h₁ (b : Fin 2) := congrArg (fun t => pastingIntervalVertex b ≫ t)
    (threeSquareInclusion_shared_first.{u})
  have h₂ (b : Fin 2) := congrArg (fun t => pastingIntervalVertex b ≫ t)
    (threeSquareInclusion_shared_second.{u})
  fin_cases e
  · change pastingIntervalVertex 0 ≫
        (pastingSquareHorizontal 0 ≫ threeSquareInclusion 0) =
      pastingIntervalVertex 0 ≫ (pastingSquareVertical 0 ≫ threeSquareInclusion 2)
    calc
      _ = pastingIntervalVertex 0 ≫
          pastingSquareVertical 0 ≫ threeSquareInclusion 0 := by
        rw [← Category.assoc, pastingSquareHorizontal_start, Category.assoc]
      _ = pastingIntervalVertex 0 ≫
          pastingSquareVertical 0 ≫ threeSquareInclusion 1 := h₁ 0
      _ = pastingIntervalVertex 0 ≫
          pastingSquareHorizontal 0 ≫ threeSquareInclusion 1 := by
        rw [← Category.assoc, pastingSquareVertical_start, Category.assoc]
      _ = pastingIntervalVertex 0 ≫
          pastingSquareHorizontal 0 ≫ threeSquareInclusion 2 := h₂ 0
      _ = _ := by
        rw [← Category.assoc, pastingSquareHorizontal_start, Category.assoc]
  · change pastingIntervalVertex 0 ≫
        (pastingSquareHorizontal 1 ≫ threeSquareInclusion 0) =
      pastingIntervalVertex 0 ≫ (pastingSquareHorizontal 1 ≫ threeSquareInclusion 1)
    simpa only [← Category.assoc, pastingSquareHorizontal_start] using h₁ 1
  · change pastingIntervalVertex 0 ≫
        (pastingSquareVertical 1 ≫ threeSquareInclusion 1) =
      pastingIntervalVertex 0 ≫ (pastingSquareVertical 1 ≫ threeSquareInclusion 2)
    simpa only [← Category.assoc, pastingSquareVertical_start] using h₂ 1

/-- 元の二脚を全次数で貼った外側ホーン。 -/
def threeSquareSpanHorn (e : Fin 3) : (Λ[2, 0] : SSet.{u}) ⟶ threeSquarePasting :=
  Classical.choose (horn₂₀.isPushout.exists_desc
    (threeSquareSpanLeft.{u} e) (threeSquareSpanRight.{u} e) (by
      simpa only [stdSimplex.δ_one_eq_const, pastingIntervalVertex] using
        threeSquareSpan_start.{u} e))

/-- 第一脚を元の包含との合成として厳密に回収する。 -/
lemma threeSquareSpanHorn_left (e : Fin 3) :
    horn₂₀.ι₀₁ ≫ threeSquareSpanHorn.{u} e = threeSquareSpanLeft e :=
  (Classical.choose_spec (horn₂₀.isPushout.exists_desc
    (threeSquareSpanLeft.{u} e) (threeSquareSpanRight.{u} e) (by
      simpa only [stdSimplex.δ_one_eq_const, pastingIntervalVertex] using
        threeSquareSpan_start.{u} e))).1

/-- 第二脚も元の包含との合成として厳密に回収する。 -/
lemma threeSquareSpanHorn_right (e : Fin 3) :
    horn₂₀.ι₀₂ ≫ threeSquareSpanHorn.{u} e = threeSquareSpanRight e :=
  (Classical.choose_spec (horn₂₀.isPushout.exists_desc
    (threeSquareSpanLeft.{u} e) (threeSquareSpanRight.{u} e) (by
      simpa only [stdSimplex.δ_one_eq_const, pastingIntervalVertex] using
        threeSquareSpan_start.{u} e))).2

end SerrePositivity.KST.SConstruction
