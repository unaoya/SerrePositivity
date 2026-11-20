module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceFirstBead
public import Mathlib.Data.List.Basic

/-! # 全 necklace の preferred form
概要：有限 joints の元の necklace を、正の長さの bead の反復連結に分解する。
方針：最初の正の joint を取り除き、元の長さについて強く帰納する。
規約：空列は一点。使われ方：原典の preferred bead wedge と元の全入力との比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction


/-- 標準 bead の有限列を、元の有限 joints の反復 wedge として読む。 -/
def ofBeads : List ℕ → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape
  | [] => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0
  | n :: ns => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedge (ofBeads ns)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (ofBeads)


/-- 空の bead 列は元の一点。 -/
lemma ofBeads_nil : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads [] = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0 := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (ofBeads_nil)


/-- bead を一つ先頭に加える作用は元の wedge。 -/
lemma ofBeads_cons (n : ℕ) (ns : List ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads (n :: ns) = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (ofBeads_cons)


/-- bead 一つの preferred form は元の標準単体一つの形。 -/
lemma ofBeads_singleton (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads [n] = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_single_zero _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (ofBeads_singleton)


/-- 元の全 necklace は、正の長さの bead の反復連結と厳密に等しい。 -/
theorem exists_positive_beads (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns = T := by
  suffices h : ∀ k, ∀ T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape, T.vertexMax = k →
      ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns = T by
    exact h T.vertexMax T rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro T hk
    by_cases h0 : T.vertexMax = 0
    · exact ⟨[], by simp, (T.eq_single_zero h0).symm⟩
    · have hn : 0 < T.vertexMax := by omega
      let p := T.firstPositiveJoint hn
      have hp : p ∈ T.joints := T.firstPositiveJoint_mem hn
      have hlt : (T.tail p hp).vertexMax < k := by
        rw [← hk]
        exact T.firstPositive_tail_lt hn
      obtain ⟨ns, hns, he⟩ := ih (T.tail p hp).vertexMax hlt (T.tail p hp) rfl
      refine ⟨p :: ns, ?_, ?_⟩
      · intro n hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact T.firstPositiveJoint_pos hn
        · exact hns n hmem
      · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads_cons, he]
        exact T.single_wedge_tail p hp (T.firstPositiveJoint_le hn)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (exists_positive_beads)


/-- 元の全 necklace の preferred bead 列。存在証明から選ぶが元の形を変えない。 -/
noncomputable def beads (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : List ℕ := (T.exists_positive_beads).choose

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (beads)


/-- 選んだ元の preferred 列の各 bead は正の長さを持つ。 -/
lemma beads_positive (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : ∀ n ∈ T.beads, 0 < n :=
  (T.exists_positive_beads).choose_spec.1

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (beads_positive)


/-- 選んだ preferred bead 列の反復 wedge は元の長さと全 joints を厳密に回収する。 -/
lemma ofBeads_beads (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads T.beads = T :=
  (T.exists_positive_beads).choose_spec.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (ofBeads_beads)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
