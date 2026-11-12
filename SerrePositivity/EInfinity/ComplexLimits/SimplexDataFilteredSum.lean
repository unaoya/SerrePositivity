module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
概要：元の全切断和・線形境界の比較から、実三相データの全 HA を証明する。
方針：元の零・中央・二相の全成分を比較し、同じ実単体の方程式を戻す。
規約：面・退化自然性と大域的な接合は別工程。使われ方：大域評価三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

lemma gradedHom_sum_heq_of_filter {ι : Type*}
    {x y x' y' : D} {k : ℤ} (hx : x = x') (hy : y = y')
    (K : Finset ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → GradedHom A x y k) (g : ι → GradedHom A x' y' k)
    (hin : HEq (∑ j ∈ K.filter P, f j) (∑ j ∈ K.filter P, g j))
    (hout : ∀ j ∈ K, ¬ P j → HEq (f j) (g j)) :
    HEq (∑ j ∈ K, f j) (∑ j ∈ K, g j) := by
  classical
  cases hx
  cases hy
  apply heq_of_eq
  have hi := eq_of_heq hin
  have ho : (∑ j ∈ K.filter (fun j => ¬ P j), f j) =
      ∑ j ∈ K.filter (fun j => ¬ P j), g j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact eq_of_heq (hout j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
  rw [← Finset.sum_filter_add_sum_filter_not K P f,
    ← Finset.sum_filter_add_sum_filter_not K P g, hi, ho]

end SerrePositivity.EInfinity.ComplexLimits
