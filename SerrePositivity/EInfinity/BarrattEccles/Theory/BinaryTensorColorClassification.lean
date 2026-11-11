module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColorAction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorPermutation
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic

/-!
# 二色パターンの軌道と安定化群

## 概要
HA 3.2.4.7 の自由代数の指定比較に必要な色付き入力の補題。

## 方針
色のファイバーの濃度、標準パターン、既存の二色部分群を同じ規約で照合する。

## 規約
任意の入力複体の微分を保ち、既存の指定包含と指定置換を使う。

## 使われ方
色付き Schur 分解から二色の係数比較への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section BinaryTensorColorOrbits
namespace SerrePositivity.EInfinity

/-- 二つの色のファイバーの濃度が等しければ、入力語は同じ置換軌道にある。 -/
lemma binaryTensorWord_exists_permutation (n : ℕ) (w z : BinaryTensorWord n)
    (h : ∀ b : Bool,
      Fintype.card {i : Fin n // binaryTensorWordColors n w i = b} =
        Fintype.card {i : Fin n // binaryTensorWordColors n z i = b}) :
    ∃ σ : Equiv.Perm (Fin n), σ • w = z := by
  classical
  let e := fun b : Bool => Fintype.equivOfCardEq (h b)
  let σ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv e
  refine ⟨σ, (binaryTensorWordColorsEquiv n).injective ?_⟩
  funext i
  change binaryTensorWordColors n (σ • w) i = binaryTensorWordColors n z i
  rw [binaryTensorWordColors_smul]
  have hi := Equiv.ofFiberEquiv_map e (σ.symm i)
  simpa only [σ, Equiv.apply_symm_apply] using hi.symm

/-- 語を固定することは、置換が各位置の色を保つことと同値。 -/
lemma binaryTensorWord_smul_eq_iff (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : BinaryTensorWord n) :
    σ • w = w ↔ ∀ i, binaryTensorWordColors n w (σ i) = binaryTensorWordColors n w i := by
  constructor
  · intro h i
    have hi := congrFun (congrArg (binaryTensorWordColors n) h) (σ i)
    simpa only [binaryTensorWordColors_smul, Equiv.symm_apply_apply] using hi.symm
  · intro h
    apply (binaryTensorWordColorsEquiv n).injective
    funext i
    change binaryTensorWordColors n (σ • w) i = binaryTensorWordColors n w i
    rw [binaryTensorWordColors_smul]
    simpa only [Equiv.apply_symm_apply] using (h (σ.symm i)).symm

end SerrePositivity.EInfinity
end BinaryTensorColorOrbits

section BinaryTensorStandardPattern
namespace SerrePositivity.EInfinity

/-- 左と右の Fin のブロックで指定する標準二色パターン。 -/
def binaryTensorStandardPattern (m n : ℕ) : BinaryTensorWord (m + n) :=
  binaryTensorWordOfColors (m + n) (Fin.addCases (fun _ => false) (fun _ => true))

/-- 標準パターンの左の位置は、false のファイバーを尽くす。 -/
def binaryTensorStandardLeftIso (m n : ℕ) :
    Fin m ≃ {i : Fin (m + n) //
      binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) i = false} := by
  let f : Fin m → {i : Fin (m + n) //
      binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) i = false} :=
    fun i => ⟨i.castAdd n, by simp [binaryTensorStandardPattern]⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin (m + n) => k.val) (congrArg Subtype.val h)
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact ⟨i, Subtype.ext rfl⟩
    | right i => simp [binaryTensorStandardPattern] at hi

/-- 標準パターンの右の位置は、true のファイバーを尽くす。 -/
def binaryTensorStandardRightIso (m n : ℕ) :
    Fin n ≃ {i : Fin (m + n) //
      binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) i = true} := by
  let f : Fin n → {i : Fin (m + n) //
      binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) i = true} :=
    fun i => ⟨i.natAdd m, by simp [binaryTensorStandardPattern]⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel
      (congrArg (fun k : Fin (m + n) => k.val) (congrArg Subtype.val h))
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => simp [binaryTensorStandardPattern] at hi
    | right i => exact ⟨i, Subtype.ext rfl⟩

/-- 標準パターンの二つの色のファイバーの濃度。 -/
lemma binaryTensorStandardPattern_card (m n : ℕ) (b : Bool) :
    Fintype.card {i : Fin (m + n) //
      binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) i = b} =
        if b then n else m := by
  cases b
  · simpa using (Fintype.card_congr (binaryTensorStandardLeftIso m n)).symm
  · simpa using (Fintype.card_congr (binaryTensorStandardRightIso m n)).symm

/-- 二色部分群のブロック置換は標準パターンを固定する。 -/
lemma binaryTensorStandardPattern_block_fixed (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    FiniteBijection.blockEquiv σ τ • binaryTensorStandardPattern m n =
      binaryTensorStandardPattern m n := by
  rw [binaryTensorWord_smul_eq_iff]
  intro i
  induction i using Fin.addCases with
  | left i => simp [blockEquiv_apply_left, binaryTensorStandardPattern]
  | right i => simp [blockEquiv_apply_right, binaryTensorStandardPattern]

end SerrePositivity.EInfinity
end BinaryTensorStandardPattern

section BinaryTensorStabilizer
namespace SerrePositivity.EInfinity
variable (m n : ℕ) (σ : Equiv.Perm (Fin (m + n)))
  (h : σ • binaryTensorStandardPattern m n = binaryTensorStandardPattern m n)

/-- 標準パターンを固定する置換の左のブロックへの制限。 -/
def binaryTensorStandardLeftPerm : Equiv.Perm (Fin m) :=
  ((binaryTensorStandardLeftIso m n).trans
    (σ.subtypeEquiv (fun i => by
      rw [(binaryTensorWord_smul_eq_iff (m + n) σ _).mp h i]))).trans
    (binaryTensorStandardLeftIso m n).symm

/-- 標準パターンを固定する置換の右のブロックへの制限。 -/
def binaryTensorStandardRightPerm : Equiv.Perm (Fin n) :=
  ((binaryTensorStandardRightIso m n).trans
    (σ.subtypeEquiv (fun i => by
      rw [(binaryTensorWord_smul_eq_iff (m + n) σ _).mp h i]))).trans
    (binaryTensorStandardRightIso m n).symm

/-- 左のブロックへの制限は元の置換の値を保つ。 -/
lemma binaryTensorStandardLeftPerm_apply (i : Fin m) :
    (binaryTensorStandardLeftPerm m n σ h i).castAdd n = σ (i.castAdd n) := by
  have hi := (binaryTensorStandardLeftIso m n).apply_symm_apply
    ((σ.subtypeEquiv (fun j => by
      rw [(binaryTensorWord_smul_eq_iff (m + n) σ _).mp h j]))
        (binaryTensorStandardLeftIso m n i))
  exact congrArg Subtype.val hi

/-- 右のブロックへの制限は元の置換の値を保つ。 -/
lemma binaryTensorStandardRightPerm_apply (i : Fin n) :
    (binaryTensorStandardRightPerm m n σ h i).natAdd m = σ (i.natAdd m) := by
  have hi := (binaryTensorStandardRightIso m n).apply_symm_apply
    ((σ.subtypeEquiv (fun j => by
      rw [(binaryTensorWord_smul_eq_iff (m + n) σ _).mp h j]))
        (binaryTensorStandardRightIso m n i))
  exact congrArg Subtype.val hi

/-- 標準パターンを固定する置換は、二つのブロックへの制限で復元される。 -/
lemma binaryTensorStandard_fix_eq_block :
    σ = FiniteBijection.blockEquiv
      (binaryTensorStandardLeftPerm m n σ h) (binaryTensorStandardRightPerm m n σ h) := by
  apply Equiv.ext
  intro i
  induction i using Fin.addCases with
  | left i =>
    rw [blockEquiv_apply_left]
    exact (binaryTensorStandardLeftPerm_apply m n σ h i).symm
  | right i =>
    rw [blockEquiv_apply_right]
    exact (binaryTensorStandardRightPerm_apply m n σ h i).symm

/-- 指定された二色部分群は、標準パターンの安定化群そのものである。 -/
lemma binaryTensorStandard_mem_twoColor_iff :
    (ULift.up σ : ULift.{u} (Equiv.Perm (Fin (m + n)))) ∈
      (BarrattEccles.twoColorPermutationHom.{u} m n).range ↔
        σ • binaryTensorStandardPattern m n = binaryTensorStandardPattern m n := by
  constructor
  · rintro ⟨g, hg⟩
    have he := congrArg ULift.down hg
    change FiniteBijection.blockEquiv g.down.1 g.down.2 = σ at he
    rw [← he]
    exact binaryTensorStandardPattern_block_fixed m n _ _
  · intro h
    refine ⟨ULift.up (binaryTensorStandardLeftPerm m n σ h,
      binaryTensorStandardRightPerm m n σ h), ?_⟩
    apply ULift.ext
    exact (binaryTensorStandard_fix_eq_block m n σ h).symm

end SerrePositivity.EInfinity
end BinaryTensorStabilizer
