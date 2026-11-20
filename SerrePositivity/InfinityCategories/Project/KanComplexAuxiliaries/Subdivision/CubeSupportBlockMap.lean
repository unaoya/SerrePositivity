module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeSupportPartition

/-! # 順序つき support ブロックを表す単調全射
概要：空でない出力の昇順列挙により、元の support の各ブロックを単調全射の fiber にする。
方針：出力部分型の順序同型を使い、割当の一意性・単調性・全射性を移す。
規約：零入力の場合は零出力への全射。使われ方：残余射の隣接 connection による実現。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 空でない support を持つ元の出力の昇順列挙。 -/
def cubeSupportOutputEmbedding {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card ↪o Fin m :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).orderEmbOfFin rfl

/-- 元の入力を、属する support ブロックの番号へ送る写像。 -/
def cubeSupportBlockMap {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : Fin n → Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card :=
  fun i => ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).symm
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSubtype h i)

/-- ブロック番号から元の出力座標を厳密に回収する。 -/
lemma cubeSupportBlockMap_output {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h i) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput h i := by
  exact congrArg Subtype.val
    (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSubtype h i))

/-- 元の support ブロックを表す写像は単調。 -/
lemma cubeSupportBlockMap_monotone {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : Monotone (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).symm.monotone.comp
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSubtype_monotone h)

/-- 元の support ブロックを表す写像は全射。 -/
lemma cubeSupportBlockMap_surjective {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h) := by
  intro a
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSubtype_surjective h
    (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).orderIsoOfFin rfl) a)
  refine ⟨i, ?_⟩
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap]
  rw [hi]
  exact ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).symm_apply_apply a

/-- 単調全射の各 fiber は、元の出力の support そのもの。 -/
lemma cubeSupportBlockMap_fiber {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (i : Fin n) (a : Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h i = a ↔
      i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s a) := by
  constructor
  · intro hi
    have heq := congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s) hi
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_output] at heq
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_eq_iff h i _).mp heq
  · intro hi
    apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s).injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_output]
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutput_eq_iff h i _).mpr hi

/-- 元の各 support ブロックは、間の入力も全て含む区間。 -/
lemma cubeSupportBlockMap_interval {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) {i j k : Fin n}
    (hij : i ≤ j) (hjk : j ≤ k) (a : Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card)
    (hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h i = a) (hk : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h k = a) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h j = a := by
  apply le_antisymm
  · simpa only [hk] using _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_monotone h hjk
  · simpa only [hi] using _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_monotone h hij

/-- ブロックの fiber max は、隣接 connection だけで実現される。 -/
lemma cubeSupportBlockMap_connectionGenerated {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeConnectionGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_connectionGenerated _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_monotone h)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_surjective h)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
