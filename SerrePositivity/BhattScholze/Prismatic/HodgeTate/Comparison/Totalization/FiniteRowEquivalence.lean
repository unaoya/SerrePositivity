module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.SingleHorizontalRow
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TruncationNaturality
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalSplitExact
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionDerived
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# 有限横行の積全複体と完全関手

## 概要
有限横行の図式の各行で完全関手後に同型となる射は、同じ Tot でも同型となる。

## 方針
最後の一行を切断の短完全列で取り出し、導来圏の完全三角形の五項補題で帰納する。

## 規約
行の内部次数は無限でよい。全複体の比較自体にシフト可換性を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部の各行の完備化単位。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 全ての横行が零なら、同じ指定全複体も零である。 -/
theorem total_isZero_of_rows (K : CochainComplex (Complex R) ℕ)
    (hK : ∀ n : ℕ, IsZero (K.X n)) : IsZero (total K) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext q
  apply component_hom_ext
  intro n
  exact ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) (q-n)).map_isZero
    (hK n)).eq_of_tgt _ _

/-- シフトと可換な関手は、関手後に同型となる射のシフトも同型にする。 -/
theorem isIso_map_shift_of_isIso_map
    (G : Complex R ⥤ ConcreteDerivedCategory R) [G.CommShift ℤ]
    {K M : Complex R} (g : K ⟶ M) (t : ℤ) [IsIso (G.map g)] :
    IsIso (G.map (g⟦t⟧')) := by
  apply (NatIso.isIso_map_iff (G.commShiftIso t) g).mpr
  change IsIso ((shiftFunctor (ConcreteDerivedCategory R) t).map (G.map g))
  infer_instance

/-- 横一行の場合の、同じ指定全複体での関手後の同型判定。 -/
theorem isIso_map_total_of_single_row
    (F : ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R) [F.CommShift ℤ]
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m))
    (hM : ∀ m : ℕ, m ≠ n → IsZero (M.X m))
    (hg : IsIso (F.map (DerivedCategory.Q.map (g.f n)))) :
    IsIso (F.map (DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g))) := by
  let G := DerivedCategory.Q ⋙ F
  haveI : IsIso (G.map (g.f n)) := hg
  haveI := isIso_map_shift_of_isIso_map G (g.f n) (-(n : ℤ))
  have hn := congrArg G.map (singleHorizontalRowProjection_naturality g n hK hM)
  simp only [Functor.map_comp] at hn
  haveI : IsIso (G.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) ≫
      G.map (singleHorizontalRowProjection M n hM)) := by
    rw [hn]
    infer_instance
  change IsIso (G.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g))
  exact IsIso.of_isIso_comp_right _ (G.map (singleHorizontalRowProjection M n hM))

/-- 有限横行での各行の同型性は、完全関手後の指定 Tot の同型性を与える。 -/
theorem isIso_map_total_of_finite_rows
    (F : ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R) [F.CommShift ℤ]
    [F.IsTriangulated] (N : ℕ)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M)
    (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hM : ∀ n : ℕ, N ≤ n → IsZero (M.X n))
    (hg : ∀ n : ℕ, IsIso (F.map (DerivedCategory.Q.map (g.f n)))) :
    IsIso (F.map (DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g))) := by
  induction N generalizing K M with
  | zero =>
    exact (F.map_isZero (DerivedCategory.Q.map_isZero (total_isZero_of_rows K (fun n => hK n (by omega))))).isIso
      (F.map_isZero (DerivedCategory.Q.map_isZero (total_isZero_of_rows M (fun n => hM n (by omega))))) _
  | succ N ih =>
    have hHead : ∀ n : ℕ,
        IsIso (F.map (DerivedCategory.Q.map ((RowTruncation.headMap g N).f n))) := by
      intro n
      by_cases hn : n < N
      · change IsIso (F.map (DerivedCategory.Q.map (if h : n < N then _ else 0)))
        rw [dif_pos hn, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
        haveI := hg n
        infer_instance
      · haveI := (RowTruncation.head_isZero K N n (by omega)).isIso
          (RowTruncation.head_isZero M N n (by omega)) ((RowTruncation.headMap g N).f n)
        infer_instance
    have htK : ∀ m : ℕ, m ≠ N → IsZero ((RowTruncation.tail K N).X m) := by
      intro m hm
      by_cases hmn : m < N
      · exact RowTruncation.tail_isZero K N m hmn
      · exact (hK m (by omega)).of_iso (RowTruncation.tailXIso K N m (by omega))
    have htM : ∀ m : ℕ, m ≠ N → IsZero ((RowTruncation.tail M N).X m) := by
      intro m hm
      by_cases hmn : m < N
      · exact RowTruncation.tail_isZero M N m hmn
      · exact (hM m (by omega)).of_iso (RowTruncation.tailXIso M N m (by omega))
    have hTail : IsIso (F.map (DerivedCategory.Q.map ((RowTruncation.tailMap g N).f N))) := by
      change IsIso (F.map (DerivedCategory.Q.map (if h : N ≤ N then _ else 0)))
      rw [dif_pos (le_refl N), Functor.map_comp, Functor.map_comp,
        Functor.map_comp, Functor.map_comp]
      haveI := hg N
      infer_instance
    have hiTail := isIso_map_total_of_single_row F (RowTruncation.tailMap g N) N htK htM hTail
    have hiHead := ih (RowTruncation.headMap g N)
      (RowTruncation.head_isZero K N) (RowTruncation.head_isZero M N) hHead
    let T := cochainProductTotalizationFunctor (ModuleCat.{u} R)
    let SK := (RowTruncation.shortComplex K N).map T
    let SM := (RowTruncation.shortComplex M N).map T
    have hSK := total_shortExact_of_rowSplitting (RowTruncation.shortComplex K N)
      (RowTruncation.rowSplitting K N)
    have hSM := total_shortExact_of_rowSplitting (RowTruncation.shortComplex M N)
      (RowTruncation.rowSplitting M N)
    let φ := F.mapTriangle.map (DerivedCategory.triangleOfSES.map hSK hSM
      (T.mapShortComplex.map (RowTruncation.shortComplexMap g N)))
    exact isIso₂_of_isIso₁₃ φ
      (F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hSK))
      (F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hSM)) hiTail hiHead

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
