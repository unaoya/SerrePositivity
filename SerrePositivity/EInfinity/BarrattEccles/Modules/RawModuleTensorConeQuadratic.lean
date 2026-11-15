module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeCutSupport

/-!
概要：実 cone の HA 右辺の非線形部分は一つの実切断合成だけである。
方針：元の内部点の全有限和で、最後から二番目以外の項を消す。
規約：元の符号と同じ切断合成を保つ。使われ方：混合 HA 方程式の最終合成項の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_quadratic_single {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (strictRawModuleTensorConeData A X P Q c).quadraticBoundary I a b k =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (penultimate I hI) •
      (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.quadraticBoundary
  apply Finset.sum_eq_single (penultimate I hI)
  · intro j hj hne
    obtain ⟨hjI, haj, hjb⟩ := Finset.mem_filter.mp hj
    rw [strictRawModuleTensorConeData_cutCompose_of_ne_penultimate A X P Q c I a b k hI ha hb hk
      j hjI haj hjb hne, smul_zero]
  · intro hnot
    exfalso
    apply hnot
    exact Finset.mem_filter.mpr ⟨penultimate_mem I hI,
      by rw [ha]; exact min_lt_penultimate I hI hc,
      by rw [hb]; exact penultimate_lt_max I hI⟩

end SerrePositivity.EInfinity.BarrattEccles
