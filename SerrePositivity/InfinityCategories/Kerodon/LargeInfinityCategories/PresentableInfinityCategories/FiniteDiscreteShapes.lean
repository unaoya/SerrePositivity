module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KappaFilteredUniverse
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：有限離散 nerve とその宇宙持ち上げは、非退化単体で数えて有限。
方針：全正次元単体の退化を示し、零次元を元の有限型で数える。
規約：各次数の有限性だけを使って全体の有限性を推測しない。
使われ方：固定始域圏の有限部分余積を全有限余極限の入口で扱う。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 離散 nerve の正次元の単体は全て退化する。 -/
lemma discreteNerve_hasDimensionLT_one (B : Type u) :
    (nerve (Discrete B)).HasDimensionLT 1 := by
  constructor
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    ext s
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [SSet.degenerate_eq_iUnion_range_σ]
    refine Set.mem_iUnion.mpr ⟨0, Set.mem_range.mpr ⟨(nerve (Discrete B)).δ 0 s, ?_⟩⟩
    have hconst (i : Fin (n + 2)) : s.obj i = s.obj 0 :=
      congrArg Discrete.mk (Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le i)))).symm
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    rw [nerve.σ_obj, nerve.δ_obj]
    exact (hconst _).trans (hconst _).symm

/-- 有限離散 nerve は有限単体集合。 -/
lemma discreteNerve_finite (B : Type u) [Finite B] : (nerve (Discrete B)).Finite := by
  have := discreteNerve_hasDimensionLT_one B
  have : Finite ((nerve (Discrete B)) _⦋0⦌) := Finite.of_equiv (Discrete B) nerveEquiv.symm
  apply SSet.finite_of_hasDimensionLT _ 1
  intro i hi
  have h : i = 0 := by omega
  subst i
  infer_instance

/-- 有限離散 nerve の同じ宇宙持ち上げも有限単体集合。 -/
lemma uliftDiscreteNerve_finite (B : Type u) [Finite B] :
    ((SSet.uliftFunctor.{v, u}).obj (nerve (Discrete B))).Finite := by
  have := discreteNerve_finite B
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff _).mp
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_ulift_iff.{u, v} Cardinal.aleph0 (nerve (Discrete B))).mpr
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff _).mpr inferInstance)
  simpa only [Cardinal.lift_aleph0] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
