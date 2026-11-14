module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! # 有限単体集合の相対骨格の停止

概要：有限な標的の相対骨格は、有限次数で標的全体になる。
方針：非退化単体の次元上界を取り、骨格への包含を全非退化単体で検査する。
規約：相対骨格の像による定義を使う。使われ方：有限対の係数充填の帰納の終端。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial

/-- 次元上界まで達した相対骨格は全体である。 -/
lemma relativeSkeleton_eq_top {L K : SSet.{u}} (i : L ⟶ K) (d : ℕ)
    [K.HasDimensionLT d] : skeletonOfMono i d = ⊤ := by
  apply (Subcomplex.eq_top_iff_of_hasDimensionLT _ d).mpr
  intro n hn s hs
  exact (skeleton_le_skeletonOfMono i d) _ (K.mem_skeleton s hn)

/-- 有限な単体集合への任意の写像の相対骨格は有限次数で停止する。 -/
lemma finiteRelativeSkeleton_exists_top {L K : SSet.{u}} (i : L ⟶ K) [K.Finite] :
    ∃ d : ℕ, skeletonOfMono i d = ⊤ := by
  obtain ⟨d, hd⟩ := K.hasDimensionLT_of_finite
  let := hd
  exact ⟨d, relativeSkeleton_eq_top i d⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
