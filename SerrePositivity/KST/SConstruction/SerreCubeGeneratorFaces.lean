module
public import SerrePositivity.KST.SConstruction.SerreCubeGenerators
public import SerrePositivity.KST.SConstruction.SerreCubeFaceNormal

/-! # 元の全 tensor 生成元を表す標準面
概要：元の端点・辺 tensor の各生成元に、その自由座標数と元の標準面表示を対応させる。
方針：元の端点は point、元の辺は keep として同じ tensor 順に読む。
規約：元の標準面と座標順を保持。使われ方：全生成元を部分集合 bead と合成へ戻す。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の tensor 生成元の辺の個数、すなわち元の自由座標数。 -/
def serreCubeGeneratorFreeDimension : (n : ℕ) → SerreCubeGeneratorIndex n → ℕ
  | 0, _ => 0
  | n + 1, (i, ⟨0, _⟩) => serreCubeGeneratorFreeDimension n i
  | n + 1, (i, ⟨1, _⟩) => serreCubeGeneratorFreeDimension n i
  | n + 1, (i, ⟨_ + 2, _⟩) => serreCubeGeneratorFreeDimension n i + 1

/-- 元の全 tensor 生成元の次数は、同じ元の自由座標数の負値。 -/
lemma serreCubeGeneratorDegree_freeDimension (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    serreCubeGeneratorDegree n i = -(serreCubeGeneratorFreeDimension n i : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    fin_cases j <;>
      simp only [serreCubeGeneratorDegree, serreCubeGeneratorFreeDimension,
        serreIntervalGeneratorDegree, ih, Nat.cast_add, Nat.cast_one] <;> omega

/-- 元の全 tensor 生成元を、同じ元の端点挿入・座標保持の標準面として読む。 -/
def serreCubeGeneratorFaceNormal : (n : ℕ) → (i : SerreCubeGeneratorIndex n) →
    CubeFaceNormal (serreCubeGeneratorFreeDimension n i) n
  | 0, _ => .nil
  | n + 1, (i, ⟨0, _⟩) => .point false (serreCubeGeneratorFaceNormal n i)
  | n + 1, (i, ⟨1, _⟩) => .point true (serreCubeGeneratorFaceNormal n i)
  | n + 1, (i, ⟨_ + 2, _⟩) => .keep (serreCubeGeneratorFaceNormal n i)

end SerrePositivity.KST.SConstruction
