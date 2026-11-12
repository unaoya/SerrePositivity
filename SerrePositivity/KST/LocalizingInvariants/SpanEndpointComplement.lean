module

public import SerrePositivity.KST.LocalizingInvariants.SpanEndpointShape
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialHornRestrictionLifting

/-!
概要：span の終点部分の外にある単体は共通始点から始まる。
方針：horn の単体が二番目・三番目の頂点だけを含むなら定値であることを示す。
規約：全次数の単体を扱う。使われ方：終点制限の cocartesian 外ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def spanApexVertex : (horn 2 0 : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn 0 0 _⟩

lemma span_simplex_constant_of_first_ne_zero {n : ℕ}
    (s : (horn 2 0 : SSet.{u}) _⦋n⦌) (hs : s.val 0 ≠ 0) (k : Fin (n + 1)) :
    s.val k = s.val 0 := by
  obtain ⟨j, hj, hjr⟩ := (mem_horn_iff_notMem_range s.val 0).mp s.property
  have h0j : s.val 0 ≠ j := fun h => hjr ⟨0, h⟩
  have hkj : s.val k ≠ j := fun h => hjr ⟨k, h⟩
  have hle := (stdSimplex.asOrderHom s.val).monotone (show (0 : Fin (n + 1)) ≤ k from Fin.zero_le k)
  apply Fin.ext
  have h0 := (s.val 0).isLt
  have hk := (s.val k).isLt
  have hnj := j.isLt
  have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
  have hs' : (s.val 0).val ≠ 0 := fun h => hs (Fin.ext h)
  have h0j' : (s.val 0).val ≠ j.val := fun h => h0j (Fin.ext h)
  have hkj' : (s.val k).val ≠ j.val := fun h => hkj (Fin.ext h)
  change (s.val 0).val ≤ (s.val k).val at hle
  omega

lemma span_simplex_mem_endpoints_of_first_ne_zero {n : ℕ}
    (s : (horn 2 0 : SSet.{u}) _⦋n⦌) (hs : s.val 0 ≠ 0) :
    s ∈ Set.range (spanEndpointInclusion.app (Opposite.op ⦋n⦌)) := by
  by_cases h1 : s.val 0 = 1
  · refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 0⟩ :
        (boundary 1 : SSet.{u}) _⦋0⦌) n, ?_⟩
    apply Subtype.ext
    apply stdSimplex.ext
    intro k
    change (1 : Fin 3) = s.val k
    exact (span_simplex_constant_of_first_ne_zero s hs k).trans h1 |>.symm
  · have h2 : s.val 0 = 2 := by
      apply Fin.ext
      change (s.val 0).val = 2
      have h0 := (s.val 0).isLt
      have hs' : (s.val 0).val ≠ 0 := fun h => hs (Fin.ext h)
      have h1' : (s.val 0).val ≠ 1 := fun h => h1 (Fin.ext h)
      omega
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 1⟩ :
        (boundary 1 : SSet.{u}) _⦋0⦌) n, ?_⟩
    apply Subtype.ext
    apply stdSimplex.ext
    intro k
    change (2 : Fin 3) = s.val k
    exact (span_simplex_constant_of_first_ne_zero s hs k).trans h2 |>.symm

lemma span_simplex_firstVertex_of_not_endpoints {n : ℕ}
    (s : (horn 2 0 : SSet.{u}) _⦋n⦌)
    (hs : s ∉ Set.range (spanEndpointInclusion.app (Opposite.op ⦋n⦌))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s = spanApexVertex := by
  have h : s.val 0 = 0 := by
    by_contra h
    exact hs (span_simplex_mem_endpoints_of_first_ne_zero s h)
  apply Subtype.ext
  apply stdSimplex.ext
  intro k
  change s.val 0 = 0
  exact h

end SerrePositivity.KST.LocalizingInvariants
