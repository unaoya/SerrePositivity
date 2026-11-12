module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleSwapSign

/-!
# shuffle の全混合境界項の有限和の消滅

概要：隣接ステップが異種である全境界項の符号付き有限和を零にする。
方針：交換を固定点のない対合とし、既に検証した実混合境界項の相殺を使う。
規約：KST Construction A.5。係数の加法群に二倍写像の単射性を仮定しない。
使われ方：shuffle の鎖写像性の混合境界和。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory

/-- 概要：隣接する二ステップが異種である shuffle と内部の面の添字。
方針：水平・垂直属性が逆であることを有限な対の部分型で表す。
規約：KST A.5、全ステップ数 n+2。
使われ方：混合境界項を対合で対にする。 -/
abbrev MixedShuffleIndex (p n : ℕ) :=
  {z : ShuffleIndex p (n + 2) × Fin (n + 1) // z.2.castSucc ∈ z.1.val ↔ z.2.succ ∉ z.1.val}

/-- 概要：混合境界項の隣接する二つのステップを交換する。
方針：水平集合を交換の置換で移す。
規約：KST A.5、面番号は保つ。使われ方：混合境界項の対合。 -/
def MixedShuffleIndex.swap {p n : ℕ} (z : MixedShuffleIndex p n) : MixedShuffleIndex p n :=
  ⟨(z.val.1.swapSteps z.val.2.castSucc z.val.2.succ, z.val.2), by
    rw [ShuffleIndex.mem_swapSteps, ShuffleIndex.mem_swapSteps,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    have h := z.property
    tauto⟩

/-- 概要：混合境界項の交換は対合。
方針：水平集合の交換を二回行う公式を使う。
規約：KST A.5。使われ方：有限和の対による相殺。 -/
@[simp] lemma MixedShuffleIndex.swap_swap {p n : ℕ} (z : MixedShuffleIndex p n) :
    z.swap.swap = z := by
  apply Subtype.ext
  apply Prod.ext
  · exact z.val.1.swapSteps_swapSteps z.val.2.castSucc z.val.2.succ
  · rfl

/-- 概要：異種ステップの交換は添字を固定しない。
方針：同じ水平集合なら隣接する二ステップの所属は同じになり矛盾する。
規約：KST A.5。使われ方：係数に二倍の単射性を要求しない有限和の相殺。 -/
lemma MixedShuffleIndex.swap_ne_self {p n : ℕ} (z : MixedShuffleIndex p n) : z.swap ≠ z := by
  intro he
  have hs := congrArg (fun z : MixedShuffleIndex p n ↦ z.val.1) he
  have ht := congrArg (fun s : ShuffleIndex p (n + 2) ↦ z.val.2.castSucc ∈ s.val) hs
  change (z.val.2.castSucc ∈ (z.val.1.swapSteps z.val.2.castSucc z.val.2.succ).val) =
    (z.val.2.castSucc ∈ z.val.1.val) at ht
  rw [propext (z.val.1.mem_swapSteps _ _ _), Equiv.swap_apply_left] at ht
  have h := z.property
  have hi := Iff.of_eq ht
  tauto

/-- 概要：面の符号と shuffle の符号を含む混合境界項の実写像。
方針：格子路の退化写像に内部の面を後合成する。
規約：KST A.5、係数は任意の単体的整数加群。
使われ方：全混合境界項の有限和。 -/
def shuffleMixedWeight (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {p q n : ℕ} (h : p + q = n + 2) (z : MixedShuffleIndex p n) :=
  (-1 : ℤ) ^ ((z.val.2 : ℕ) + 1) •
    ((-1 : ℤ) ^ z.val.1.inversions •
      (integerTensorMap (C.map z.val.1.left.op) (D.map (z.val.1.right h).op) ≫
        integerTensorMap (C.δ z.val.2.succ.castSucc) (D.δ z.val.2.succ.castSucc)))

/-- 概要：水平・垂直の順の混合項と交換した項の和は零。
方針：実テンソル写像の相殺に、共通する面の符号を掛ける。
規約：KST A.5。使われ方：対合による全混合境界和の消滅。 -/
lemma shuffleMixedWeight_cancel_of_left (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {p q n : ℕ} (h : p + q = n + 2) (z : MixedShuffleIndex p n)
    (ha : z.val.2.castSucc ∈ z.val.1.val) :
    shuffleMixedWeight C D h z + shuffleMixedWeight C D h z.swap = 0 := by
  have hb := z.property.mp ha
  have hc := shuffleSwapMixedFace_cancel C D z.val.1 h z.val.2 ha hb
  have ht := congrArg (fun v ↦ (-1 : ℤ) ^ ((z.val.2 : ℕ) + 1) • v) hc
  rw [smul_add, smul_zero] at ht
  change shuffleMixedWeight C D h z.swap + shuffleMixedWeight C D h z = 0 at ht
  simpa only [add_comm] using ht

/-- 概要：全ての混合項は交換した相手の項と相殺する。
方針：二つの順序の一方へ帰着し、対合性を使う。
規約：KST A.5、水平・垂直の両順序を含む。
使われ方：全混合境界和に対する有限和の対合。 -/
lemma shuffleMixedWeight_cancel (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {p q n : ℕ} (h : p + q = n + 2) (z : MixedShuffleIndex p n) :
    shuffleMixedWeight C D h z + shuffleMixedWeight C D h z.swap = 0 := by
  by_cases ha : z.val.2.castSucc ∈ z.val.1.val
  · exact shuffleMixedWeight_cancel_of_left C D h z ha
  · have hb : z.val.2.succ ∈ z.val.1.val := by
      have ht := z.property
      tauto
    have hs : z.swap.val.2.castSucc ∈ z.swap.val.1.val := by
      change z.val.2.castSucc ∈ (z.val.1.swapSteps z.val.2.castSucc z.val.2.succ).val
      rw [ShuffleIndex.mem_swapSteps, Equiv.swap_apply_left]
      exact hb
    have ht := shuffleMixedWeight_cancel_of_left C D h z.swap hs
    rw [MixedShuffleIndex.swap_swap] at ht
    simpa only [add_comm] using ht

/-- 概要：shuffle の全ての混合境界項の符号付き有限和は零。
方針：固定点のない交換対合と実写像の各対の相殺を有限和へ適用する。
規約：KST Construction A.5、任意の加法群の整数加群で成立。
使われ方：shuffle の実鎖写像性の混合面の部分。 -/
theorem shuffleMixed_sum_zero (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {p q n : ℕ} (h : p + q = n + 2) :
    ∑ z : MixedShuffleIndex p n, shuffleMixedWeight C D h z = 0 := by
  classical
  exact Finset.sum_involution (s := Finset.univ) (f := shuffleMixedWeight C D h)
    (fun (z : MixedShuffleIndex p n) _ ↦ z.swap)
    (fun z _ ↦ shuffleMixedWeight_cancel C D h z)
    (fun z _ _ ↦ z.swap_ne_self)
    (fun z _ ↦ Finset.mem_univ z.swap)
    (fun z _ ↦ z.swap_swap)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
