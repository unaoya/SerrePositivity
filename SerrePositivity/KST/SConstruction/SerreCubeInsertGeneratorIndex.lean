module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorRightIndex
public import SerrePositivity.KST.SConstruction.SerreCubeFaceGeneratorIndex

/-! # 元の任意の tensor 生成元への指定座標の端点挿入
概要：任意の元の生成元添字に、元の右端座標で指定した端点を挿入する。
方針：右端では端点を追加し、内側では元の最右因子をそのまま保って再帰する。
規約：元の座標順と生成元を保持。使われ方：全生成元上の面制限と微分像の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の右端からの指定座標に端点を挿入し、元の他の全因子を保つ添字。 -/
def serreCubeInsertGeneratorIndex (b : Bool) : (n : ℕ) → Fin (n + 1) →
    SerreCubeGeneratorIndex n → SerreCubeGeneratorIndex (n + 1)
  | 0, _, i => (i, serreCubeGeneratorEndpointIndex b)
  | n + 1, q, (i, j) => Fin.cases
      ((i, j), serreCubeGeneratorEndpointIndex b)
      (fun q => (serreCubeInsertGeneratorIndex b n q i, j)) q

/-- 元の右端への挿入は、元の生成元の最後への同じ端点追加。 -/
lemma serreCubeInsertGeneratorIndex_zero (b : Bool) (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    serreCubeInsertGeneratorIndex b n 0 i = (i, serreCubeGeneratorEndpointIndex b) := by
  cases n with
  | zero => rfl
  | succ n => obtain ⟨i, j⟩ := i; rfl

/-- 元の内側の挿入は、前段の挿入後も元の最右因子を保つ。 -/
lemma serreCubeInsertGeneratorIndex_succ (b : Bool) (n : ℕ) (q : Fin (n + 1))
    (i : SerreCubeGeneratorIndex n) (j : Fin 3) :
    serreCubeInsertGeneratorIndex b (n + 1) q.succ (i, j) =
      (serreCubeInsertGeneratorIndex b n q i, j) := rfl

/-- 元の任意座標への端点挿入は、元の自由座標数を変えない。 -/
lemma serreCubeInsertGeneratorIndex_freeDimension (b : Bool) (n : ℕ) (q : Fin (n + 1))
    (i : SerreCubeGeneratorIndex n) :
    serreCubeGeneratorFreeDimension (n + 1) (serreCubeInsertGeneratorIndex b n q i) =
      serreCubeGeneratorFreeDimension n i := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    refine Fin.cases ?_ (fun q => ?_) q
    · change serreCubeGeneratorFreeDimension (n + 1 + 1)
        ((i, j), serreCubeGeneratorEndpointIndex b) = _
      cases b <;> rfl
    · rw [serreCubeInsertGeneratorIndex_succ]
      fin_cases j
      · exact ih q i
      · exact ih q i
      · exact congrArg (· + 1) (ih q i)

/-- 元の任意座標への端点挿入は、元の生成元次数を変えない。 -/
lemma serreCubeInsertGeneratorIndex_degree (b : Bool) (n : ℕ) (q : Fin (n + 1))
    (i : SerreCubeGeneratorIndex n) :
    serreCubeGeneratorDegree (n + 1) (serreCubeInsertGeneratorIndex b n q i) =
      serreCubeGeneratorDegree n i := by
  rw [serreCubeGeneratorDegree_freeDimension, serreCubeInsertGeneratorIndex_freeDimension]
  exact (serreCubeGeneratorDegree_freeDimension n i).symm

/-- 元の最高添字への任意座標の挿入は、既存の同じ一端点面添字を回収する。 -/
lemma serreCubeInsertGeneratorIndex_top (b : Bool) (n : ℕ) (q : Fin (n + 1)) :
    serreCubeInsertGeneratorIndex b n q (serreCubeTopGeneratorIndex n) =
      serreCubeFaceGeneratorIndex b n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun q => ?_) q
    · rw [serreCubeInsertGeneratorIndex_zero, serreCubeFaceGeneratorIndex_zero]
    · exact congrArg (fun i => (i, (2 : Fin 3))) (ih q)

end SerrePositivity.KST.SConstruction
