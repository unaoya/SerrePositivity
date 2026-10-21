module
public import SerrePositivity.KST.SConstruction.SerreCubeInsertGeneratorIndex

/-! # 元の零端点・辺だけを含む生成元添字の分解
概要：一端点を含まない元の生成元を、最高添字か任意位置の零端点挿入に分ける。
方針：元の最右因子から帰納し、前段の零端点の位置を保持して辺を付ける。
規約：元の生成元添字を保持。使われ方：零端点・辺の混在生成元の微分可換性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の全座標で零端点または辺だけを選んだ、元の生成元添字の条件。 -/
def SerreCubeZeroEdgeIndex : (n : ℕ) → SerreCubeGeneratorIndex n → Prop
  | 0, _ => True
  | n + 1, (i, j) => SerreCubeZeroEdgeIndex n i ∧ (j = 0 ∨ j = 2)

/-- 元の正次元の零端点・辺添字は、最高添字か同じ条件の前段への零端点挿入。 -/
lemma serreCubeZeroEdgeIndex_cases (n : ℕ) (i : SerreCubeGeneratorIndex (n + 1))
    (hi : SerreCubeZeroEdgeIndex (n + 1) i) :
    i = serreCubeTopGeneratorIndex (n + 1) ∨
      ∃ (q : Fin (n + 1)) (j : SerreCubeGeneratorIndex n),
        SerreCubeZeroEdgeIndex n j ∧ i = serreCubeInsertGeneratorIndex false n q j := by
  induction n with
  | zero =>
    obtain ⟨i, j⟩ := i
    rcases hi.2 with rfl | rfl
    · exact Or.inr ⟨0, i, hi.1, rfl⟩
    · left
      cases i
      rfl
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    rcases hi.2 with rfl | rfl
    · exact Or.inr ⟨0, i, hi.1, (serreCubeInsertGeneratorIndex_zero false (n + 1) i).symm⟩
    · rcases ih i hi.1 with ht | ⟨q, j, hj, he⟩
      · exact Or.inl (congrArg (fun i => (i, (2 : Fin 3))) ht)
      · exact Or.inr ⟨q.succ, (j, 2), ⟨hj, Or.inr rfl⟩,
          congrArg (fun i => (i, (2 : Fin 3))) he⟩

/-- 元の零端点・辺条件は、元の右側全辺添字の付加で保たれる。 -/
lemma serreCubeZeroEdgeIndex_right (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (hi : SerreCubeZeroEdgeIndex n i) (t : ℕ) :
    SerreCubeZeroEdgeIndex (n + t) (serreCubeGeneratorRightIndex n i t) := by
  induction t with
  | zero => exact hi
  | succ t ih => exact ⟨ih, Or.inr rfl⟩

end SerrePositivity.KST.SConstruction
