module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces

/-! # 元の生成元添字への右側全辺付加
概要：任意の元の tensor 生成元に、指定数の元の辺添字を右に付ける。
方針：元の添字 2 の付加を反復し、自由次元と次数を同じ順で回収する。
規約：元の生成元族と tensor 順を保持。使われ方：右側頂点集合を保つ辺読み替え。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の生成元添字の右側に t 個の元の辺添字を付ける。 -/
def serreCubeGeneratorRightIndex (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    (t : ℕ) → SerreCubeGeneratorIndex (n + t)
  | 0 => i
  | t + 1 => (serreCubeGeneratorRightIndex n i t, 2)

/-- 元の右側全辺付加の自由次元は、元の自由次元と同じ付加辺数の和。 -/
lemma serreCubeGeneratorRightIndex_freeDimension (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (t : ℕ) :
    serreCubeGeneratorFreeDimension (n + t) (serreCubeGeneratorRightIndex n i t) =
      serreCubeGeneratorFreeDimension n i + t := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (· + 1) ih

/-- 元の右側全辺付加の次数は、元の次数から付加辺数を引いたもの。 -/
lemma serreCubeGeneratorRightIndex_degree (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ) :
    serreCubeGeneratorDegree (n + t) (serreCubeGeneratorRightIndex n i t) =
      serreCubeGeneratorDegree n i - (t : ℤ) := by
  have h := serreCubeGeneratorDegree_freeDimension (n + t) (serreCubeGeneratorRightIndex n i t)
  rw [serreCubeGeneratorRightIndex_freeDimension] at h
  have h₀ := serreCubeGeneratorDegree_freeDimension n i
  omega

end SerrePositivity.KST.SConstruction
