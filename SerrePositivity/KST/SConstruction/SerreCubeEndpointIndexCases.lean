module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorConcat

/-! # 元の全生成元添字の最高添字・内部端点分解
概要：元の任意添字を、最高添字または左右ブロック間の元の端点挿入へ分ける。
方針：元の最右因子が辺なら前段の分解を右へ延長し、端点ならその位置で切る。
規約：元の全因子と全次元を保持。使われ方：HA 線形復元の全生成元上の次元帰納。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

private lemma pair_heq {α β γ : Type} {a : α} {b : β} (h : HEq a b) (c : γ) :
    HEq (a, c) (b, c) := by
  cases h
  rfl

/-- 元の全添字は、最高添字か元の左右ブロック間の零・一端点挿入で表される。 -/
lemma serreCubeGenerator_endpoint_cases (M : ℕ) (a : SerreCubeGeneratorIndex M) :
    a = serreCubeTopGeneratorIndex M ∨
      ∃ (n m : ℕ) (i : SerreCubeGeneratorIndex n) (j : SerreCubeGeneratorIndex m) (b : Bool),
        M = n + 1 + m ∧
          HEq a (serreCubeGeneratorConcat (n + 1) (i, serreCubeGeneratorEndpointIndex b) m j) := by
  induction M with
  | zero =>
    left
    cases a
    rfl
  | succ M ih =>
    obtain ⟨a, k⟩ := a
    fin_cases k
    · exact Or.inr ⟨M, 0, a, PUnit.unit, false, rfl, HEq.rfl⟩
    · exact Or.inr ⟨M, 0, a, PUnit.unit, true, rfl, HEq.rfl⟩
    · rcases ih a with ht | ⟨n, m, i, j, b, hd, he⟩
      · exact Or.inl (congrArg (fun a => (a, (2 : Fin 3))) ht)
      · exact Or.inr ⟨n, m + 1, i, (j, 2), b,
          (congrArg Nat.succ hd), pair_heq he 2⟩

/-- 元の次元と添字が一致すれば、元の生成元次数も一致する。 -/
lemma serreCubeGeneratorDegree_heq {n m : ℕ} (hn : n = m)
    (i : SerreCubeGeneratorIndex n) (j : SerreCubeGeneratorIndex m) (hi : HEq i j) :
    serreCubeGeneratorDegree n i = serreCubeGeneratorDegree m j := by
  cases hn
  cases hi
  rfl

end SerrePositivity.KST.SConstruction
