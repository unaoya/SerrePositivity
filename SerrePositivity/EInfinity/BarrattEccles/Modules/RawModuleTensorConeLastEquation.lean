module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeRhsMixedLast
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConePairEquation

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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_of_last_mem {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (hlast : Fin.last (n + 1) ∈ I) :
    (strictRawModuleTensorConeData A X P Q c).Equation I := by
  by_cases h0 : (0 : Fin (n + 2)) ∈ I
  · by_cases hc : I.card = 2
    · exact strictRawModuleTensorConeData_equation_pair A X P Q c I hc
    · intro a b k hI ha hb hk
      have hc3 : 3 ≤ I.card := by omega
      have ha0 : a = 0 := ha.trans
        ((I.isLeast_min' _).unique ⟨h0, fun _ _ => Fin.zero_le _⟩)
      have hbl : b = Fin.last (n + 1) := hb.trans
        ((I.isGreatest_max' _).unique ⟨hlast, fun _ _ => Fin.le_last _⟩)
      have hd := strictRawModuleTensorConeData_d_mixed_last A X P Q c I a b k hI ha hb hk ha0 hbl h0
      have hr := strictRawModuleTensorConeData_rhs_mixed_last A X P Q c I a b k hI ha hb hk
        hc3 ha0 hbl h0
      exact eq_of_heq (hd.trans hr.symm)
  · exact strictRawModuleTensorConeData_equation_without_zero A X P Q c I h0

end SerrePositivity.EInfinity.BarrattEccles
