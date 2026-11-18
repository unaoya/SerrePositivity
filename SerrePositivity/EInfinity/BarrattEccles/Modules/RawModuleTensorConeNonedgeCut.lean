module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryZero
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearBoundary

/-!
概要：通常側の切断集合が二点以外なら、実 cone の HA 項は削除項だけになる。
方針：同じ通常成分の零と dg 合成の零を使い、元の削除成分を回収する。
規約：元の符号・有限集合・内部点を保持する。
使われ方：混合右辺を全線形削除和と最後の切断に分ける。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_term_of_nonedge_cut {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).term I a b k hI ha hb hk j hj haj hjb =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j) a b (k + 1) := by
  have hamin : IsLeast (I : Set (Fin (n + 2))) a := by rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 2))) b := by rw [hb]; exact I.isGreatest_max' _
  have hz := strictRawModuleTensorConeData_hom_ordinary_zero A X P Q c (I.filter (j ≤ ·)) j b
    (2 - ((I.filter (j ≤ ·)).card : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le _) rfl
    (ne_of_gt ((Fin.zero_le a).trans_lt haj)) hc
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term]
  rw [hz, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two hamin.1 hbmax.1 haj hjb)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min hamin haj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max hbmax hjb _)
    (by have := Finset.card_erase_add_one hj; omega)]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
