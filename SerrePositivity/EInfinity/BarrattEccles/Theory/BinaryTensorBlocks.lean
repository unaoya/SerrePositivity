module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColorAction
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic

/-!
# 二色の標準ブロックのテンソル

## 概要
HA 3.2.4.7 の二色の係数比較の入力を、左因子と右因子の標準順序へそろえる。

## 方針
右だけの語の前へ左の色を付ける。テンソルの括弧は結合子だけでそろえる。

## 規約
左の m 因子の後に右の n 因子を並べ、空のブロックも含める。

## 使われ方
二色部分群の標準入力と、誘導表示の基準の語。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.TensorPowers

/-- 右因子だけからなる入力語。 -/
def binaryTensorRightWord : ∀ n, BinaryTensorWord n
  | 0 => PUnit.unit
  | n + 1 => .inr (binaryTensorRightWord n)

/-- 左の m 因子の後に右の n 因子を並べた標準入力語。 -/
def binaryTensorBlockWord : ∀ m n, BinaryTensorWord (m + n)
  | 0, n => cast (congrArg BinaryTensorWord (Nat.zero_add n).symm)
      (binaryTensorRightWord n)
  | m + 1, n => cast (congrArg BinaryTensorWord (Nat.succ_add m n).symm)
      (.inl (binaryTensorBlockWord m n))

/-- 右だけの語では、全ての位置の色は右である。 -/
@[simp]
lemma binaryTensorRightWord_colors : ∀ n (i : Fin n),
    binaryTensorWordColors n (binaryTensorRightWord n) i = true := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  (X Y : C)

/-- 右だけの語のテンソルは、右因子のテンソル冪である。 -/
def binaryTensorRightWordIso : ∀ n,
    binaryTensorWordObj X Y n (binaryTensorRightWord n) ≅ power Y n
  | 0 => Iso.refl _
  | n + 1 => whiskerLeftIso Y (binaryTensorRightWordIso n)

/-- arity の添字の等式に沿って入力語のテンソルを移す。 -/
def binaryTensorWordCastIso {r s : ℕ} (h : r = s) (w : BinaryTensorWord r) :
    binaryTensorWordObj X Y s (cast (congrArg BinaryTensorWord h) w) ≅
      binaryTensorWordObj X Y r w := by
  subst s
  exact Iso.refl _

/-- 標準入力語のテンソルを、左右のテンソル冪のテンソルへそろえる。 -/
def binaryTensorBlockWordIso : ∀ m n,
    binaryTensorWordObj X Y (m + n) (binaryTensorBlockWord m n) ≅ power X m ⊗ power Y n
  | 0, n =>
    binaryTensorWordCastIso X Y (Nat.zero_add n).symm (binaryTensorRightWord n) ≪≫
      binaryTensorRightWordIso X Y n ≪≫ (λ_ (power Y n)).symm
  | m + 1, n =>
    binaryTensorWordCastIso X Y (Nat.succ_add m n).symm (.inl (binaryTensorBlockWord m n)) ≪≫
      whiskerLeftIso X (binaryTensorBlockWordIso m n) ≪≫
        (α_ X (power X m) (power Y n)).symm

end SerrePositivity.EInfinity
