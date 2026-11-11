module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap

/-!
概要：標準単体の fat join の円柱の二つの変形の有限順序集合上の写像。
方針：一端で左成分を最後の頂点、零端で右成分を零へ移す。
規約：ホモトピーの時間はもう一つの Fin 2 とする。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間の一端で左成分を最後の頂点に移す単調写像。
方針：零端では元の値、一端では最大元とする。
規約：第一因子は標準 n 単体の頂点。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形。 -/
def leftClamp (n : ℕ) : Fin (n + 1) × Fin 2 →o Fin (n + 1) where
  toFun p := if p.2 = 0 then p.1 else Fin.last n
  monotone' p q h := by
    by_cases hq : q.2 = 0
    · have hp : p.2 = 0 := Fin.ext (by
        have ht : p.2.val ≤ q.2.val := h.2
        rw [hq] at ht
        omega)
      dsimp only
      rw [if_pos hp, if_pos hq]
      exact h.1
    · dsimp only
      rw [if_neg hq]
      exact Fin.le_last _

/-- 概要：区間の零端で右成分を零へ移す単調写像。
方針：零端では最小元、一端では元の値とする。
規約：第一因子は標準 n 単体の頂点。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形。 -/
def rightClamp (n : ℕ) : Fin (n + 1) × Fin 2 →o Fin (n + 1) where
  toFun p := if p.2 = 0 then 0 else p.1
  monotone' p q h := by
    by_cases hp : p.2 = 0
    · dsimp only
      rw [if_pos hp]
      exact Fin.zero_le _
    · have hq : q.2 ≠ 0 := by
        intro hq
        apply hp
        apply Fin.ext
        have ht : p.2.val ≤ q.2.val := h.2
        rw [hq] at ht
        omega
      dsimp only
      rw [if_neg hp, if_neg hq]
      exact h.1

/-- 概要：左成分の変形の時間を含む単調写像。
方針：元の区間座標と時間座標の最小値を使う。
規約：時間零は恒等、時間一は leftClamp。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な変形の構成。 -/
def leftClampHom (n : ℕ) : (Fin (n + 1) × Fin 2) × Fin 2 →o Fin (n + 1) where
  toFun p := leftClamp n (p.1.1, min p.1.2 p.2)
  monotone' _ _ h := (leftClamp n).monotone ⟨h.1.1, min_le_min h.1.2 h.2⟩

/-- 概要：右成分の変形の時間を含む単調写像。
方針：元の区間座標と時間座標の最大値を使う。
規約：時間零は rightClamp、時間一は恒等。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な変形の構成。 -/
def rightClampHom (n : ℕ) : (Fin (n + 1) × Fin 2) × Fin 2 →o Fin (n + 1) where
  toFun p := rightClamp n (p.1.1, max p.1.2 p.2)
  monotone' _ _ h := (rightClamp n).monotone ⟨h.1.1, max_le_max h.1.2 h.2⟩

/-- 概要：左成分の変形は零端で恒等。
方針：条件式の零の分岐を計算する。
規約：任意の頂点 a。
使われ方：Kerodon §4.6.2（Tag 01HM） の左因子の固定。 -/
lemma leftClamp_zero (n : ℕ) (a : Fin (n + 1)) : leftClamp n (a, 0) = a := rfl

/-- 概要：左成分の変形は一端で最後の頂点。
方針：条件式の非零の分岐を計算する。
規約：区間座標は Fin 2 の一。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱の右側の正規化。 -/
lemma leftClamp_one (n : ℕ) (a : Fin (n + 1)) : leftClamp n (a, 1) = Fin.last n := by
  change (if (1 : Fin 2) = 0 then a else Fin.last n) = Fin.last n
  rw [if_neg (by decide)]

/-- 概要：右成分の変形は零端で零。
方針：条件式の零の分岐を計算する。
規約：任意の頂点 a。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱の左側の正規化。 -/
lemma rightClamp_zero (n : ℕ) (a : Fin (n + 1)) : rightClamp n (a, 0) = 0 := rfl

/-- 概要：右成分の変形は一端で恒等。
方針：条件式の非零の分岐を計算する。
規約：区間座標は Fin 2 の一。
使われ方：Kerodon §4.6.2（Tag 01HM） の右因子の固定。 -/
lemma rightClamp_one (n : ℕ) (a : Fin (n + 1)) : rightClamp n (a, 1) = a := by
  change (if (1 : Fin 2) = 0 then 0 else a) = a
  rw [if_neg (by decide)]

/-- 概要：左成分のホモトピーの時間零は恒等。
方針：最小値の零と左変形の零端を計算する。
規約：元の区間座標は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形の始点。 -/
lemma leftClampHom_zero (n : ℕ) (a : Fin (n + 1)) (t : Fin 2) :
    leftClampHom n ((a, t), 0) = a := by
  change leftClamp n (a, min t 0) = a
  rw [min_eq_right (Fin.zero_le _), leftClamp_zero]

/-- 概要：左成分のホモトピーの時間一は左変形。
方針：区間の最大元との最小値を計算する。
規約：Fin 2 の一は最大元。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形の終点。 -/
lemma leftClampHom_one (n : ℕ) (a : Fin (n + 1)) (t : Fin 2) :
    leftClampHom n ((a, t), 1) = leftClamp n (a, t) := by
  change leftClamp n (a, min t 1) = _
  have ht : t ≤ (1 : Fin 2) := by have := t.isLt; change t.val ≤ 1; omega
  rw [min_eq_left ht]

/-- 概要：右成分のホモトピーの時間零は右変形。
方針：最小元との最大値を計算する。
規約：元の区間座標は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形の始点。 -/
lemma rightClampHom_zero (n : ℕ) (a : Fin (n + 1)) (t : Fin 2) :
    rightClampHom n ((a, t), 0) = rightClamp n (a, t) := by
  change rightClamp n (a, max t 0) = _
  rw [max_eq_left (Fin.zero_le _)]

/-- 概要：右成分のホモトピーの時間一は恒等。
方針：最大元との最大値と右変形の一端を計算する。
規約：Fin 2 の一は最大元。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形の終点。 -/
lemma rightClampHom_one (n : ℕ) (a : Fin (n + 1)) (t : Fin 2) :
    rightClampHom n ((a, t), 1) = a := by
  change rightClamp n (a, max t 1) = a
  have ht : t ≤ (1 : Fin 2) := by have := t.isLt; change t.val ≤ 1; omega
  rw [max_eq_right ht, rightClamp_one]

/-- 概要：左の変形の族は元の区間の零端を常に固定する。
方針：零との最小値と leftClamp の零端を計算する。
規約：時間座標は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の左因子を固定したホモトピー。 -/
lemma leftClampHom_fixed_zero (n : ℕ) (a : Fin (n + 1)) (s : Fin 2) :
    leftClampHom n ((a, 0), s) = a := by
  change leftClamp n (a, min 0 s) = a
  rw [min_eq_left (Fin.zero_le _), leftClamp_zero]

/-- 概要：右の変形の族は元の区間の一端を常に固定する。
方針：一との最大値と rightClamp の一端を計算する。
規約：時間座標は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の右因子を固定したホモトピー。 -/
lemma rightClampHom_fixed_one (n : ℕ) (a : Fin (n + 1)) (s : Fin 2) :
    rightClampHom n ((a, 1), s) = a := by
  change rightClamp n (a, max 1 s) = a
  have hs : s ≤ (1 : Fin 2) := by have := s.isLt; change s.val ≤ 1; omega
  rw [max_eq_left hs, rightClamp_one]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
