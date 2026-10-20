module
public import SerrePositivity.KST.SConstruction.DGStandardHomMap

/-! # 厳密 dg 関手の標準 DK 単位・AW 合成の保存
概要：標準 DK Hom 上の全単体への作用が元の単位と AW 合成を保つ。
方針：AW の全切断点の斉次合成を同じ dg 関手で写し、単位は各有限集合で計算する。
規約：AW の切断順序と元の dg 単位を保持する。使われ方：単体的豊穣関手の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DoldKanComparison DGNerve.PinchedHom
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E]

/-- 元の Hom chain map は全切断点の AW 成分族を保つ。 -/
lemma dgStandardDataMap_aw (F : DGFunctor A D E) {x y z : D} {n : ℕ}
    (g : LinearData A y z n) (f : LinearData A x y n) :
    dgStandardDataMap F (awData g f) = awData (dgStandardDataMap F g) (dgStandardDataMap F f) := by
  funext i
  simp only [dgStandardDataMap, awData, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact DGNerve.map_compose F _ _ _

/-- 厳密 dg 関手は、元の標準単体の AW 合成を厳密に保存する。 -/
lemma dgStandardSimplexMap_aw (F : DGFunctor A D E) {x y z : D} {n : ℕ}
    (g : StandardSimplex A y z n) (f : StandardSimplex A x y n) :
    dgStandardSimplexMap F (standardAW g f) =
      standardAW (dgStandardSimplexMap F g) (dgStandardSimplexMap F f) :=
  Subtype.ext (dgStandardDataMap_aw F g.val f.val)

/-- 厳密 dg 関手は、元の dg 単位の全標準定数単体を厳密に保存する。 -/
lemma dgStandardSimplexMap_unit (F : DGFunctor A D E) (x : D) (n : ℕ) :
    dgStandardSimplexMap F (standardUnit (R := A) x n) =
      standardUnit (R := A) (F.obj x) n := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change J.Nonempty at hJ
  change k = 1 - (J.card : ℤ) at hk
  change (F.map x x).f k
      ((standardConstant (unitElement A x) n).val.component J k hJ hk) =
    (standardConstant (unitElement A (F.obj x)) n).val.component J k hJ hk
  by_cases hc : 2 ≤ J.card
  · rw [standardConstant_component_zero _ _ _ _ _ hc,
      standardConstant_component_zero _ _ _ _ _ hc, map_zero]
  · have hcard : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hk₀ : k = 0 := by simpa using hk
    rcases hk₀ with rfl
    rw [standardConstant_singleton, standardConstant_singleton]
    exact DGFunctor.map_unitElement A F x

end SerrePositivity.KST.SConstruction
