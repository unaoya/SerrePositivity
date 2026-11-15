module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TailBounds

/-!
# 非負横次数での有限頭部と尾部

## 概要
各行の内部次数を切らず、横次数だけを頭部と尾部へ分ける。

## 方針
CochainComplex.of と指定された項の同型で微分を定める。

## 規約
切断は項ごとの切断であり、良い切断ではない。

## 使われ方
BS 著者版 Lemma 4.22 の有限切断と、横次数が大きい尾部の下界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped ZeroObject

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]
namespace RowTruncation
variable (K : CochainComplex (Complex R) ℕ) (N : ℕ)

/-- 有限頭部の第 n 行。 -/
def headX (n : ℕ) : Complex R := if n < N then K.X n else 0

/-- 頭部に残る元の行との指定同型。 -/
def headXIso (n : ℕ) (h : n < N) : headX K N n ≅ K.X n :=
  eqToIso (ite_eq_left h)

/-- 有限頭部の隣接微分。 -/
def headStep (n : ℕ) : headX K N n ⟶ headX K N (n+1) :=
  if h : n+1 < N then
    (headXIso K N n (by omega)).hom ≫ K.d n (n+1) ≫ (headXIso K N (n+1) h).inv
  else 0

/-- 頭部の指定した隣接微分の二乗は零。 -/
theorem headStep_sq (n : ℕ) : headStep K N n ≫ headStep K N (n+1) = 0 := by
  by_cases h : n+1+1 < N
  · rw [headStep, dite_eq_left (show n+1 < N by omega), headStep, dite_eq_left h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (K.d n (n+1)), HomologicalComplex.d_comp_d, zero_comp, comp_zero]
  · simp only [headStep, dite_eq_right h, comp_zero]

/-- n < N の行だけを残す有限頭部。 -/
def head : CochainComplex (Complex R) ℕ :=
  CochainComplex.of (headX K N) (headStep K N) (headStep_sq K N)

/-- 尾部の第 n 行。 -/
def tailX (n : ℕ) : Complex R := if N ≤ n then K.X n else 0

/-- 尾部に残る元の行との指定同型。 -/
def tailXIso (n : ℕ) (h : N ≤ n) : tailX K N n ≅ K.X n :=
  eqToIso (ite_eq_left h)

/-- 尾部の隣接微分。 -/
def tailStep (n : ℕ) : tailX K N n ⟶ tailX K N (n+1) :=
  if h : N ≤ n then
    (tailXIso K N n h).hom ≫ K.d n (n+1) ≫ (tailXIso K N (n+1) (by omega)).inv
  else 0

/-- 尾部の指定した隣接微分の二乗は零。 -/
theorem tailStep_sq (n : ℕ) : tailStep K N n ≫ tailStep K N (n+1) = 0 := by
  by_cases h : N ≤ n
  · rw [tailStep, dite_eq_left h, tailStep, dite_eq_left (show N ≤ n+1 by omega)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (K.d n (n+1)), HomologicalComplex.d_comp_d, zero_comp, comp_zero]
  · simp only [tailStep, dite_eq_right h, zero_comp]

/-- N ≤ n の行だけを残す尾部。 -/
def tail : CochainComplex (Complex R) ℕ :=
  CochainComplex.of (tailX K N) (tailStep K N) (tailStep_sq K N)

/-- 元の図式から有限頭部への標準射影。 -/
def projection : K ⟶ head K N where
  f n := if h : n < N then (headXIso K N n h).inv else 0
  comm' i j hij := by
    change i+1 = j at hij
    subst j
    change (if h : i < N then (headXIso K N i h).inv else 0) ≫
      CochainComplex.of.d (headX K N) (headStep K N) i (i+1) =
        K.d i (i+1) ≫ (if h : i+1 < N then (headXIso K N (i+1) h).inv else 0)
    rw [CochainComplex.of_d]
    by_cases h : i+1 < N
    · rw [dite_eq_left (show i < N by omega), headStep, dite_eq_left h, dite_eq_left h]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · rw [headStep, dite_eq_right h, dite_eq_right h, comp_zero, comp_zero]

/-- 尾部から元の図式への標準包含。 -/
def inclusion : tail K N ⟶ K where
  f n := if h : N ≤ n then (tailXIso K N n h).hom else 0
  comm' i j hij := by
    change i+1 = j at hij
    subst j
    change (if h : N ≤ i then (tailXIso K N i h).hom else 0) ≫ K.d i (i+1) =
      CochainComplex.of.d (tailX K N) (tailStep K N) i (i+1) ≫
        (if h : N ≤ i+1 then (tailXIso K N (i+1) h).hom else 0)
    rw [CochainComplex.of_d]
    by_cases h : N ≤ i
    · rw [dite_eq_left h, tailStep, dite_eq_left h, dite_eq_left (show N ≤ i+1 by omega)]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [dite_eq_right h, tailStep, dite_eq_right h, zero_comp, zero_comp]

/-- 切り落とした高い行の頭部は零対象である。 -/
theorem head_isZero (n : ℕ) (h : N ≤ n) : IsZero ((head K N).X n) := by
  change IsZero (headX K N n)
  rw [headX, ite_eq_right (by omega)]
  exact isZero_zero _

/-- 切り落とした低い行の尾部は零対象である。 -/
theorem tail_isZero (n : ℕ) (h : n < N) : IsZero ((tail K N).X n) := by
  change IsZero (tailX K N n)
  rw [tailX, ite_eq_right (by omega)]
  exact isZero_zero _

/-- 切断後に残る行のコホモロジーは、元の行のコホモロジーである。 -/
theorem tail_homology_lowerBound (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (n : ℕ) (hn : N ≤ n) (i : ℤ) (hi : i < b) :
    IsZero (((tail K N).X n).homology i) :=
  (hK n i hi).of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    (tailXIso K N n hn))

/-- 実際の尾部の下界は横切断次数だけ上がる。 -/
theorem total_tail_homology_lowerBound (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b) : IsZero ((total (tail K N)).homology q) :=
  total_tail_lowerBound (tail K N) N b (tail_isZero K N)
    (tail_homology_lowerBound K N b hK) q hq

end RowTruncation
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
