module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrderProfiles

/-!
概要：有限順序集合の最初の二点を併合する実射と、その切断・因子化を構成する。
方針：値を一つ下げる単調射と後続点の包含を使う。
規約：最初の二点が同じ像を持つ条件から元の全射の因子化の等式を証明する。
使われ方：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実区間の細分。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最初の二点を併合する有限単調射。
方針：自然数の値を1減らす。規約：残りの点の順序を保つ。
使われ方：Riehl–Verity §4.1の最初の折り返しを分離する射。 -/
def ordinalBottomMerge (m : ℕ) : Fin (m + 2) →o Fin (m + 1) where
  toFun i := ⟨i.val - 1, by have hi := i.isLt; omega⟩
  monotone' := by intro i j hij; exact Nat.sub_le_sub_right hij 1

/-- 概要：併合する二点のうち後の点を選ぶ実切断。
方針：後続点の包含を使う。規約：全ての点の値を1増やす。
使われ方：Riehl–Verity §4.1の実残余射の構成。 -/
def ordinalBottomMergeSection (m : ℕ) : Fin (m + 1) →o Fin (m + 2) where
  toFun i := i.succ
  monotone' := by
    intro i j hij
    change i.val + 1 ≤ j.val + 1
    exact Nat.add_le_add_right hij 1

/-- 概要：併合の射の値は自然数の値から1を引いたもの。
方針：実定義で照合する。規約：先頭0は0のまま。
使われ方：Riehl–Verity §4.1の併合の全点での照合。 -/
lemma ordinalBottomMerge_val (m : ℕ) (i : Fin (m + 2)) :
    (ordinalBottomMerge m i).val = i.val - 1 := rfl

/-- 概要：後続点の包含は併合の実切断。
方針：各点の値の加算と減算を相殺する。規約：有限単調射の等式。
使われ方：Riehl–Verity §4.1の残余射の一意性。 -/
lemma ordinalBottomMerge_section (m : ℕ) :
    (ordinalBottomMerge m).comp (ordinalBottomMergeSection m) = OrderHom.id := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change i.val + 1 - 1 = i.val
  omega

/-- 概要：最初の二点の像が同じ射は併合を通して実際に因子化する。
方針：切断との合成を残余射にし、先頭とそれ以外の点で比較する。
規約：元の全有限単調射の等式。使われ方：Riehl–Verity §4.1の実細分。 -/
lemma ordinalBottomMerge_factor {m n : ℕ} (f : Fin (m + 2) →o Fin n)
    (h : f 0 = f (0 : Fin (m + 1)).succ) :
    (f.comp (ordinalBottomMergeSection m)).comp (ordinalBottomMerge m) = f := by
  apply OrderHom.ext
  funext i
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    exact h.symm
  · have he : ordinalBottomMergeSection m (ordinalBottomMerge m i) = i := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    exact congrArg f he

/-- 概要：併合する射は最小元と最大元を保つ。
方針：最小元0と最後の値の減算を比較する。規約：両端がminusの場合の条件。
使われ方：Riehl–Verity §4.1の実Homへの併合射の回収。 -/
lemma ordinalBottomMerge_boundary (m : ℕ) :
    WalkingAdjunctionOrderBoundary .minus .minus (ordinalBottomMerge m) := by
  constructor
  · intro _ i hi
    change i.val - 1 = 0
    omega
  · intro _ i hi
    change i.val - 1 + 1 = m + 1
    omega

/-- 概要：切断から作る残余射は最小元と指定の終点の端点を保つ。
方針：二番目の点の像0と、元の最大元の保存を使う。
規約：元の射の端点条件を輸送する。使われ方：Riehl–Verity §4.1の実残余射の回収。 -/
lemma ordinalBottomMerge_residual_boundary {m n : ℕ} (Y : WalkingAdjunctionPoint)
    (f : Fin (m + 2) →o Fin n) (hf : WalkingAdjunctionOrderBoundary .minus Y f)
    (h1 : (f (0 : Fin (m + 1)).succ).val = 0) :
    WalkingAdjunctionOrderBoundary .minus Y (f.comp (ordinalBottomMergeSection m)) := by
  constructor
  · intro _ i hi
    have he : i = 0 := Fin.ext hi
    subst i
    exact h1
  · intro hY i hi
    exact hf.2 hY i.succ (by change i.val + 1 + 1 = m + 2; omega)

end SerrePositivity.InfinityCategories.HA.Monads
