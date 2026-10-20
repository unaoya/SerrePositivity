module
public import SerrePositivity.KST.SConstruction.DoubleDiagonalTrianglePasting
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 元の四面複体の交換二辺を同じ内ホーンへまとめる
概要：元の四面複体の二つの指定辺が同じ中間頂点を持つことを証明し、内ホーンへ貼る。
方針：元の対角辺・中間辺の厳密な貼り合わせと単体面の恒等式を使う。
規約：標的の Kan 性を使わず、元の二つの全区間を厳密に保持する。
使われ方：元の交換第二三角形を、元の四面複体の同じ二辺へ貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の前二射段面の上辺。 -/
def correctionPastingLower : (Δ[1] : SSet.{u}) ⟶ doubleDiagonalTrianglePasting 0 2 :=
  stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingFirst 0 2

/-- 元の後二射二部分面の上辺。 -/
def correctionPastingUpper : (Δ[1] : SSet.{u}) ⟶ doubleDiagonalTrianglePasting 0 2 :=
  stdSimplex.δ 0 ≫ triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingSecond 0 2

/-- 二つの元の全辺の共有中間頂点は、同じ実複体内で厳密に一致する。 -/
lemma correctionPasting_corner :
    stdSimplex.δ 0 ≫ correctionPastingLower.{u} =
      stdSimplex.δ 1 ≫ correctionPastingUpper.{u} := by
  have hc : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
    simpa using stdSimplex.δ_comp_δ_self (i := (0 : Fin 2))
  have hm : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  unfold correctionPastingLower correctionPastingUpper
  calc
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingFirst 0 2 := by
      simp only [← Category.assoc]
      rw [hc]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingFirst 0 2 := by
      simpa only [Category.assoc] using
        congrArg (fun q => stdSimplex.δ (0 : Fin 2) ≫ q ≫
          doubleDiagonalTrianglePastingFirst 0 2) triangleDiagonalPasting_shared.{u}
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingFirst 0 2 := by
      simp only [← Category.assoc]
      rw [hc]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingSecond 0 2 := by
      simpa only [Category.assoc] using
        congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) (doubleDiagonalTrianglePasting_shared.{u} 0 2)
    _ = _ := by
      simp only [← Category.assoc]
      rw [hm]

/-- 元の同じ交換二辺を全区間として保持する、四面複体内の指定内ホーン。 -/
def correctionPastingHorn : (Λ[2, 1] : SSet.{u}) ⟶ doubleDiagonalTrianglePasting 0 2 :=
  horn₂₁.isPushout.desc correctionPastingLower correctionPastingUpper correctionPasting_corner

/-- ホーンの第一全辺は元の同じ前二射段上辺。 -/
lemma correctionPastingHorn_lower :
    horn₂₁.ι₀₁ ≫ correctionPastingHorn.{u} = correctionPastingLower :=
  horn₂₁.isPushout.inl_desc _ _ _

/-- ホーンの第二全辺も元の同じ後二射二部分上辺。 -/
lemma correctionPastingHorn_upper :
    horn₂₁.ι₁₂ ≫ correctionPastingHorn.{u} = correctionPastingUpper :=
  horn₂₁.isPushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
