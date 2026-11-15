module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteRowEquivalence
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TruncationHomology

/-!
# 一様下界の下での行ごとの擬同型と指定積全複体

## 概要
行ごとの擬同型を、一様なコホモロジー下界の下で元の積全複体へ渡す。

## 方針
固定次数で有限頭部へ射影し、有限行の完全三角形による判定を使う。

## 規約
元の複体の内部次数の項ごとの有界性は要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の、係数制限後の指定模型の行ごとの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 行の一様下界に対し、指定 Tot から十分深い頭部への射影は固定次数で擬同型である。 -/
theorem total_projection_quasiIsoAt (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q+1 < (N : ℤ)+b) :
    QuasiIsoAt ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (RowTruncation.projection K N)) q :=
  quasiIsoAt_g_of_left_homology_zero _
    (total_shortExact_of_rowSplitting (RowTruncation.shortComplex K N) (RowTruncation.rowSplitting K N)) q
    (RowTruncation.total_tail_homology_lowerBound K N b hK q (by omega))
    (RowTruncation.total_tail_homology_lowerBound K N b hK (q+1) hq)

/-- 一様下界を持つ行ごとの擬同型は、元の指定積全複体の擬同型となる。 -/
theorem total_map_quasiIso_of_rows {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M)
    (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (hM : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((M.X n).homology i))
    (hg : ∀ n : ℕ, QuasiIso (g.f n)) :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) := by
  constructor
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨N, hN⟩ := exists_nat_gt (q+1-b)
  have hbound : q+1 < (N : ℤ)+b := by omega
  haveI := (quasiIsoAt_iff_isIso_homologyMap _ q).mp (total_projection_quasiIsoAt K N b hK q hbound)
  haveI := (quasiIsoAt_iff_isIso_homologyMap _ q).mp (total_projection_quasiIsoAt M N b hM q hbound)
  have hHead : ∀ n : ℕ, IsIso (DerivedCategory.Q.map ((RowTruncation.headMap g N).f n)) := by
    intro n
    by_cases hn : n < N
    · haveI := hg n
      haveI : QuasiIso ((RowTruncation.headMap g N).f n) := by
        change QuasiIso (if h : n < N then _ else 0)
        rw [dite_eq_left hn]
        infer_instance
      infer_instance
    · haveI := (RowTruncation.head_isZero K N n (by omega)).isIso
        (RowTruncation.head_isZero M N n (by omega)) ((RowTruncation.headMap g N).f n)
      infer_instance
  have hFin := isIso_map_total_of_finite_rows (𝟭 (ConcreteDerivedCategory R)) N
    (RowTruncation.headMap g N) (RowTruncation.head_isZero K N) (RowTruncation.head_isZero M N) hHead
  change IsIso (DerivedCategory.Q.map
    ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (RowTruncation.headMap g N))) at hFin
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mp hFin
  have hn := congrArg (fun k => homologyMap
    ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map k) q)
    (RowTruncation.projection_naturality g N)
  simp only [Functor.map_comp, homologyMap_comp] at hn
  haveI : IsIso (homologyMap ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) q ≫
      homologyMap ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (RowTruncation.projection M N)) q) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (homologyMap ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (RowTruncation.projection M N)) q)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
