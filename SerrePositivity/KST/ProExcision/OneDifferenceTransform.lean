module
public import SerrePositivity.KST.ProExcision.BlockPatternNaturality

/-!
# 非単位部分環の準同型による 1+S の単位群の射

概要：非単位部分環の準同型から 1 からの差で定まる単位部分群の準同型を作る。
方針：単位と逆の差を準同型で送り、xy の項を含む積の差の公式を使う。
規約：KST Lemma 4.16 の外部行列作用。周囲の全環の準同型への延長は要求しない。
使われ方：first n 行への左行列作用を三角ブロック群の自己準同型へ持ち上げる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：差の単位部分群の元の 1 からの差を部分環の元として与える。
方針：群の定義の第一の所属条件を使う。
規約：KST 4.16、非単位部分環。使われ方：外部行列作用の準同型の入力。 -/
def oneDifferenceElement (S : NonUnitalSubring R) (a : oneDifferenceSubgroup S) : S :=
  ⟨(a.val : R) - 1, a.property.1⟩

/-- 概要：積の差は二つの差と差の積の和。
方針：周囲の非可換環で分配展開する。
規約：KST 4.16。使われ方：非単位準同型から単位群への射の乗法保存。 -/
lemma oneDifferenceElement_mul (S : NonUnitalSubring R) (a b : oneDifferenceSubgroup S) :
    oneDifferenceElement S (a * b) = oneDifferenceElement S a + oneDifferenceElement S b +
      oneDifferenceElement S a * oneDifferenceElement S b := by
  apply Subtype.ext
  change (a.val : R) * (b.val : R) - 1 =
    ((a.val : R) - 1) + ((b.val : R) - 1) + ((a.val : R) - 1) * ((b.val : R) - 1)
  noncomm_ring

/-- 概要：単位と逆の差は x+y+xy=0 を満たす。
方針：積の差の公式を逆の積へ適用する。
規約：KST 4.16。使われ方：差の像から作る単位の逆の確認。 -/
lemma oneDifferenceElement_inv_relation (S : NonUnitalSubring R) (a : oneDifferenceSubgroup S) :
    oneDifferenceElement S a + oneDifferenceElement S a⁻¹ +
      oneDifferenceElement S a * oneDifferenceElement S a⁻¹ = 0 := by
  rw [← oneDifferenceElement_mul, mul_inv_cancel]
  apply Subtype.ext
  exact sub_self (1 : R)

/-- 概要：非単位部分環の準同型から差の単位部分群への群準同型を作る。
方針：単位と逆の差を準同型で送り、両側の逆関係と積の差を使う。
規約：KST 4.16 の外部行列作用、1 は周囲の環内でのみ使用する。
使われ方：三角部分環の行列作用の実群への持ち上げ。 -/
def oneDifferenceTransform (S : NonUnitalSubring R) (S' : NonUnitalSubring R') (f : S →ₙ+* S') :
    oneDifferenceSubgroup S →* oneDifferenceSubgroup S' where
  toFun a :=
    let x := f (oneDifferenceElement S a)
    let y := f (oneDifferenceElement S a⁻¹)
    have hxy : (x : R') + (y : R') + (x : R') * (y : R') = 0 := by
      have hz : x + y + x * y = 0 := by
        dsimp only [x, y]
        rw [← map_mul, ← map_add, ← map_add, oneDifferenceElement_inv_relation, map_zero]
      exact congrArg (fun z : S' ↦ z.val) hz
    have hyx : (y : R') + (x : R') + (y : R') * (x : R') = 0 := by
      have hz : y + x + y * x = 0 := by
        dsimp only [x, y]
        rw [← map_mul, ← map_add, ← map_add]
        have h := oneDifferenceElement_inv_relation S a⁻¹
        rw [inv_inv] at h
        rw [h, map_zero]
      exact congrArg (fun z : S' ↦ z.val) hz
    ⟨{ val := 1 + (x : R')
       inv := 1 + (y : R')
       val_inv := by
         calc
           _ = 1 + ((x : R') + (y : R') + (x : R') * (y : R')) := by noncomm_ring
           _ = 1 := by rw [hxy, add_zero]
       inv_val := by
         calc
           _ = 1 + ((y : R') + (x : R') + (y : R') * (x : R')) := by noncomm_ring
           _ = 1 := by rw [hyx, add_zero] }, by
       constructor
       · change 1 + (x : R') - 1 ∈ S'
         simpa only [add_sub_cancel_left] using x.property
       · change 1 + (y : R') - 1 ∈ S'
         simpa only [add_sub_cancel_left] using y.property⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change 1 + ((f (oneDifferenceElement S 1) : S') : R') = 1
    have h : oneDifferenceElement S 1 = 0 := by apply Subtype.ext; exact sub_self (1 : R)
    rw [h, map_zero]
    exact add_zero 1
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change 1 + ((f (oneDifferenceElement S (a * b)) : S') : R') =
      (1 + ((f (oneDifferenceElement S a) : S') : R')) * (1 + ((f (oneDifferenceElement S b) : S') : R'))
    rw [oneDifferenceElement_mul, map_add, map_add, map_mul]
    change 1 + (((f (oneDifferenceElement S a) : S') : R') + ((f (oneDifferenceElement S b) : S') : R') +
      ((f (oneDifferenceElement S a) : S') : R') * ((f (oneDifferenceElement S b) : S') : R')) = _
    noncomm_ring

end SerrePositivity.KST.ProExcision
