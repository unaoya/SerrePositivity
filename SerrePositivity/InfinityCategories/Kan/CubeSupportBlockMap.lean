module
public import SerrePositivity.InfinityCategories.Kan.CubeSupportPartition

/-! # 順序つき support ブロックを表す単調全射
概要：空でない出力の昇順列挙により、元の support の各ブロックを単調全射の fiber にする。
方針：出力部分型の順序同型を使い、割当の一意性・単調性・全射性を移す。
規約：零入力の場合は零出力への全射。使われ方：残余射の隣接 connection による実現。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 空でない support を持つ元の出力の昇順列挙。 -/
def cubeSupportOutputEmbedding {n m : ℕ} (s : CubeJoinNormalForm n m) :
    Fin (cubeSupportNonemptyOutputs s).card ↪o Fin m :=
  (cubeSupportNonemptyOutputs s).orderEmbOfFin rfl

/-- 元の入力を、属する support ブロックの番号へ送る写像。 -/
def cubeSupportBlockMap {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) : Fin n → Fin (cubeSupportNonemptyOutputs s).card :=
  fun i => ((cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).symm
    (cubeSupportOutputSubtype h i)

/-- ブロック番号から元の出力座標を厳密に回収する。 -/
lemma cubeSupportBlockMap_output {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) (i : Fin n) :
    cubeSupportOutputEmbedding s (cubeSupportBlockMap h i) = cubeSupportOutput h i := by
  exact congrArg Subtype.val
    (((cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).apply_symm_apply
      (cubeSupportOutputSubtype h i))

/-- 元の support ブロックを表す写像は単調。 -/
lemma cubeSupportBlockMap_monotone {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) : Monotone (cubeSupportBlockMap h) :=
  ((cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).symm.monotone.comp
    (cubeSupportOutputSubtype_monotone h)

/-- 元の support ブロックを表す写像は全射。 -/
lemma cubeSupportBlockMap_surjective {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) : Function.Surjective (cubeSupportBlockMap h) := by
  intro a
  obtain ⟨i, hi⟩ := cubeSupportOutputSubtype_surjective h
    (((cubeSupportNonemptyOutputs s).orderIsoOfFin rfl) a)
  refine ⟨i, ?_⟩
  dsimp only [cubeSupportBlockMap]
  rw [hi]
  exact ((cubeSupportNonemptyOutputs s).orderIsoOfFin rfl).symm_apply_apply a

/-- 単調全射の各 fiber は、元の出力の support そのもの。 -/
lemma cubeSupportBlockMap_fiber {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) (i : Fin n) (a : Fin (cubeSupportNonemptyOutputs s).card) :
    cubeSupportBlockMap h i = a ↔
      i ∈ cubeJoinNormalFormSupport s (cubeSupportOutputEmbedding s a) := by
  constructor
  · intro hi
    have heq := congrArg (cubeSupportOutputEmbedding s) hi
    rw [cubeSupportBlockMap_output] at heq
    exact (cubeSupportOutput_eq_iff h i _).mp heq
  · intro hi
    apply (cubeSupportOutputEmbedding s).injective
    rw [cubeSupportBlockMap_output]
    exact (cubeSupportOutput_eq_iff h i _).mpr hi

/-- 元の各 support ブロックは、間の入力も全て含む区間。 -/
lemma cubeSupportBlockMap_interval {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) {i j k : Fin n}
    (hij : i ≤ j) (hjk : j ≤ k) (a : Fin (cubeSupportNonemptyOutputs s).card)
    (hi : cubeSupportBlockMap h i = a) (hk : cubeSupportBlockMap h k = a) :
    cubeSupportBlockMap h j = a := by
  apply le_antisymm
  · simpa only [hk] using cubeSupportBlockMap_monotone h hjk
  · simpa only [hi] using cubeSupportBlockMap_monotone h hij

/-- ブロックの fiber max は、隣接 connection だけで実現される。 -/
lemma cubeSupportBlockMap_connectionGenerated {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) : CubeConnectionGenerated (cubeFiberMax (cubeSupportBlockMap h)) :=
  cubeFiberMax_connectionGenerated _ (cubeSupportBlockMap_monotone h)
    (cubeSupportBlockMap_surjective h)

end SerrePositivity.KST.SConstruction
