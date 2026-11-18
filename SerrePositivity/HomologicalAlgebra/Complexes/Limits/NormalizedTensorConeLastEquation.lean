module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeRhsMixedLast
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConePairEquation

/-!
概要：実 cone の終端を含む全ての有限集合で、元の HA 方程式を証明する。
方針：通常成分と二点は既存方程式へ、残る混合成分は同じ普遍線形右辺へ戻す。
規約：元の生データと全次数を保つ。使われ方：任意終端への制限と全 cone の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_equation_of_last_mem {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (hlast : Fin.last (n + 1) ∈ I) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).Equation I := by
  by_cases h0 : (0 : Fin (n + 2)) ∈ I
  · by_cases hc : I.card = 2
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_equation_pair A X Y c I hc
    · intro a b k hI ha hb hk
      have hc3 : 3 ≤ I.card := by omega
      have ha0 : a = 0 := ha.trans
        ((I.isLeast_min' _).unique ⟨h0, fun _ _ => Fin.zero_le _⟩)
      have hbl : b = Fin.last (n + 1) := hb.trans
        ((I.isGreatest_max' _).unique ⟨hlast, fun _ _ => Fin.le_last _⟩)
      have hd := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_d_mixed_last A X Y c I a b k hI ha hb hk ha0 hbl h0
      have hr := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_rhs_mixed_last A X Y c I a b k hI ha hb hk
        hc3 ha0 hbl h0
      exact eq_of_heq (hd.trans hr.symm)
  · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_equation_without_zero A X Y c I h0

end SerrePositivity.ComplexLimits
