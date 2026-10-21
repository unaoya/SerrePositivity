module
public import SerrePositivity.KST.SConstruction.SerreCubeInsertGeneratorIndex

/-! # 元の tensor 生成元添字の左右ブロック分解
概要：元の添字を指定した左右ブロックで連結・分解し、全因子と次数を保つ。
方針：右ブロックの元の最右因子を一つずつ加える再帰を用いる。
規約：元の tensor 順を保持。使われ方：内部一端点の左右線形復元との比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の左右の生成元添字を、同じ因子順に連結する。 -/
def serreCubeGeneratorConcat (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    (m : ℕ) → SerreCubeGeneratorIndex m → SerreCubeGeneratorIndex (n + m)
  | 0, _ => i
  | m + 1, (j, k) => (serreCubeGeneratorConcat n i m j, k)

/-- 元の連結添字の次数は、元の左右の次数の和。 -/
lemma serreCubeGeneratorConcat_degree (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) :
    serreCubeGeneratorDegree (n + m) (serreCubeGeneratorConcat n i m j) =
      serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j := by
  induction m with
  | zero => exact (add_zero _).symm
  | succ m ih =>
    obtain ⟨j, k⟩ := j
    exact (congrArg (· + serreIntervalGeneratorDegree k) (ih j)).trans (add_assoc _ _ _)

/-- 元の連結添字の自由次元は、元の左右の自由次元の和。 -/
lemma serreCubeGeneratorConcat_freeDimension (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) :
    serreCubeGeneratorFreeDimension (n + m) (serreCubeGeneratorConcat n i m j) =
      serreCubeGeneratorFreeDimension n i + serreCubeGeneratorFreeDimension m j := by
  have h := serreCubeGeneratorConcat_degree n i m j
  rw [serreCubeGeneratorDegree_freeDimension, serreCubeGeneratorDegree_freeDimension,
    serreCubeGeneratorDegree_freeDimension] at h
  omega

/-- 元の連結生成元添字を、指定した元の左右ブロックへ分解する。 -/
def serreCubeGeneratorSplit (n : ℕ) :
    (m : ℕ) → SerreCubeGeneratorIndex (n + m) →
      SerreCubeGeneratorIndex n × SerreCubeGeneratorIndex m
  | 0, i => (i, PUnit.unit)
  | m + 1, (i, k) =>
    let j := serreCubeGeneratorSplit n m i
    (j.1, (j.2, k))

/-- 元の連結後の分解は、元の左右添字を回収する。 -/
lemma serreCubeGeneratorSplit_concat (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) :
    serreCubeGeneratorSplit n m (serreCubeGeneratorConcat n i m j) = (i, j) := by
  induction m with
  | zero => cases j; rfl
  | succ m ih =>
    obtain ⟨j, k⟩ := j
    exact congrArg (fun p => (p.1, (p.2, k))) (ih j)

/-- 元の分解後の連結は、元の全添字を回収する。 -/
lemma serreCubeGeneratorConcat_split (n m : ℕ) (i : SerreCubeGeneratorIndex (n + m)) :
    serreCubeGeneratorConcat n (serreCubeGeneratorSplit n m i).1 m
      (serreCubeGeneratorSplit n m i).2 = i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨i, k⟩ := i
    exact congrArg (fun j => (j, k)) (ih i)

/-- 元の全生成元添字は、指定した元の左右ブロックの連結として表される。 -/
lemma serreCubeGeneratorConcat_surjective (n m : ℕ) :
    Function.Surjective (fun p : SerreCubeGeneratorIndex n × SerreCubeGeneratorIndex m =>
      serreCubeGeneratorConcat n p.1 m p.2) :=
  fun i => ⟨serreCubeGeneratorSplit n m i, serreCubeGeneratorConcat_split n m i⟩

private lemma pair_heq {α β γ : Type} {a : α} {b : β} (h : HEq a b) (c : γ) :
    HEq (a, c) (b, c) := by
  cases h
  rfl

/-- 元のブロック間の端点挿入は、元の左添字への端点追加と元の右添字の連結。 -/
lemma serreCubeGeneratorConcat_insert (b : Bool) (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) :
    HEq (serreCubeInsertGeneratorIndex b (n + m) ⟨m, by omega⟩
      (serreCubeGeneratorConcat n i m j))
      (serreCubeGeneratorConcat (n + 1) (i, serreCubeGeneratorEndpointIndex b) m j) := by
  induction m with
  | zero => exact heq_of_eq (serreCubeInsertGeneratorIndex_zero b n i)
  | succ m ih =>
    obtain ⟨j, k⟩ := j
    exact pair_heq (ih j) k

end SerrePositivity.KST.SConstruction
