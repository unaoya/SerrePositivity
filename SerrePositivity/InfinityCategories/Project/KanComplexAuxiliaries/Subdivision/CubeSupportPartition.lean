module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeConnectionGeneration

/-! # 使用入力を尽くす順序つき support と出力の割当
概要：未使用入力のない順序つき support から、各入力が属する唯一の出力を取り出す。
方針：全入力の被覆から出力を選び、順序条件から一意性と単調性を証明する。
規約：空 support の出力は選ばない。使われ方：support ブロックを表す単調全射。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 全入力を尽くし、元の出力順に厳密に並ぶ support の条件。 -/
structure CubeSupportPartition {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) : Prop where
  ordered : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s k → i < l
  covers : ∀ i, ∃ j, i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j

/-- 順序つき被覆では、一つの入力が属する出力は唯一。 -/
lemma cubeSupportPartition_unique {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) {i : Fin n} {j k : Fin m}
    (hj : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j) (hk : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s k) :
    j = k := by
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact False.elim ((lt_irrefl i) (h.ordered hjk hj hk))
  · exact hjk
  · exact False.elim ((lt_irrefl i) (h.ordered hkj hk hj))

/-- 元の入力が属する出力の選択。 -/
def cubeSupportOutput {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (i : Fin n) : Fin m :=
  Classical.choose (h.covers i)

/-- 選択した出力の support は、元の入力を含む。 -/
lemma cubeSupportOutput_mem {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (i : Fin n) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput h i) :=
  Classical.choose_spec (h.covers i)

/-- 出力の割当は、元の support への所属を厳密に回収する。 -/
lemma cubeSupportOutput_eq_iff {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (i : Fin n) (j : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput h i = j ↔ i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j := by
  constructor
  · rintro rfl
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_mem h i
  · intro hi
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportPartition_unique h (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_mem h i) hi

/-- 元の入力から出力への割当は単調。 -/
lemma cubeSupportOutput_monotone {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : Monotone (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput h) := by
  intro i l hil
  apply le_of_not_gt
  intro hlt
  exact (not_lt_of_ge hil)
    (h.ordered hlt (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_mem h l) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_mem h i))

/-- 空でない support を持つ元の出力の集合。 -/
def cubeSupportNonemptyOutputs {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j).Nonempty)

/-- 出力集合への所属は、その同じ support が空でないこと。 -/
lemma mem_cubeSupportNonemptyOutputs {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) (j : Fin m) :
    j ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s ↔ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j).Nonempty := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs]

/-- 元の入力を、空でない support を持つ出力の部分型へ送る割当。 -/
def cubeSupportOutputSubtype {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (i : Fin n) :
    {j : Fin m // j ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput h i,
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeSupportNonemptyOutputs s _).mpr ⟨i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_mem h i⟩⟩

/-- 部分型への出力割当は単調。 -/
lemma cubeSupportOutputSubtype_monotone {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : Monotone (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSubtype h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_monotone h

/-- 部分型への出力割当は、元の空でない出力を全て実現する。 -/
lemma cubeSupportOutputSubtype_surjective {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSubtype h) := by
  intro j
  obtain ⟨i, hi⟩ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeSupportNonemptyOutputs s j.val).mp j.property
  refine ⟨i, Subtype.ext ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_eq_iff h i j.val).mpr hi

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
