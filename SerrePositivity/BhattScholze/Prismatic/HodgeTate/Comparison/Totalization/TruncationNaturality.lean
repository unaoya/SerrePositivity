module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RowTruncationExact

/-!
# 横切断の射と標準短完全列の自然性

## 概要
元の図式の射を、同じ有限頭部と尾部へ制限する。

## 方針
残る行では指定行同型で共役し、消える行では零射とする。

## 規約
切断次数は固定する。横微分の境界では零対象を使う。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部に関する帰納。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.RowTruncation
variable {R : Type u} [CommRing R]
variable {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) (N : ℕ)

/-- 同じ有限頭部への制限。 -/
def headMap : head K N ⟶ head M N where
  f n := if h : n < N then
    (headXIso K N n h).hom ≫ g.f n ≫ (headXIso M N n h).inv else 0
  comm' i j hij := by
    change i+1=j at hij
    subst j
    by_cases hj : i+1 < N
    · have hi : i < N := by omega
      change (if h : i < N then _ else 0) ≫
        CochainComplex.of.d (headX M N) (headStep M N) i (i+1) =
          CochainComplex.of.d (headX K N) (headStep K N) i (i+1) ≫
            (if h : i+1 < N then _ else 0)
      simp only [dif_pos hi, dif_pos hj, CochainComplex.of_d, headStep,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [g.comm_assoc i (i+1)]
    · exact (head_isZero M N (i+1) (by omega)).eq_of_tgt _ _

/-- 同じ尾部への制限。 -/
def tailMap : tail K N ⟶ tail M N where
  f n := if h : N ≤ n then
    (tailXIso K N n h).hom ≫ g.f n ≫ (tailXIso M N n h).inv else 0
  comm' i j hij := by
    change i+1=j at hij
    subst j
    by_cases hi : N ≤ i
    · have hj : N ≤ i+1 := by omega
      change (if h : N ≤ i then _ else 0) ≫
        CochainComplex.of.d (tailX M N) (tailStep M N) i (i+1) =
          CochainComplex.of.d (tailX K N) (tailStep K N) i (i+1) ≫
            (if h : N ≤ i+1 then _ else 0)
      simp only [dif_pos hi, dif_pos hj, CochainComplex.of_d, tailStep,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [g.comm_assoc i (i+1)]
    · exact (tail_isZero K N i (by omega)).eq_of_src _ _

/-- 頭部射影は元の図式について自然である。 -/
@[reassoc] theorem projection_naturality :
    g ≫ projection M N = projection K N ≫ headMap g N := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n < N
  · change g.f n ≫ (projection M N).f n =
      (projection K N).f n ≫ (headMap g N).f n
    simp only [projection, headMap, dif_pos hn, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  · exact (head_isZero M N n (by omega)).eq_of_tgt _ _

/-- 尾部包含は元の図式について自然である。 -/
@[reassoc] theorem inclusion_naturality :
    tailMap g N ≫ inclusion M N = inclusion K N ≫ g := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : N ≤ n
  · change (tailMap g N).f n ≫ (inclusion M N).f n =
      (inclusion K N).f n ≫ g.f n
    simp only [inclusion, tailMap, dif_pos hn, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · exact (tail_isZero K N n (by omega)).eq_of_src _ _

/-- 元の射が誘導する切断短完全列の射。 -/
def shortComplexMap : shortComplex K N ⟶ shortComplex M N where
  τ₁ := tailMap g N
  τ₂ := g
  τ₃ := headMap g N
  comm₁₂ := inclusion_naturality g N
  comm₂₃ := projection_naturality g N

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.RowTruncation
