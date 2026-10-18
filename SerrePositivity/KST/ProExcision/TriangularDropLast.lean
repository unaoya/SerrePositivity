module
public import SerrePositivity.KST.ProExcision.MatrixLastColumn

/-!
# 三角ブロック群の左上ブロックへの射影

概要：最後の補助座標を落とす実群準同型を構成する。
方針：最終行の恒等性を用いて左上ブロックの積と逆を比較する。
規約：KST Claim 4.15 の半直積への分解。係数イデアルは非可換。
使われ方：T_{n,m+1} の基底 T_{n,m} の抽出。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：三角群の最終行は恒等行。
方針：既証明の最大添字の行の固定性を last に適用する。
規約：KST Claim 4.15。使われ方：左上ブロックの乗法保存。 -/
lemma triangularBlockGroup_lastRow (n m : ℕ) (J : TwoSidedIdeal R)
    (g : triangularBlockGroup n (m + 1) J) (j : Fin (n + m + 1)) :
    (g.val : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) (Fin.last (n + m)) j =
      (1 : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) (Fin.last (n + m)) j :=
  triangularBlockGroup_fixed_max_row n (m + 1) J g _ (fun _ ↦ Fin.le_last _) j

/-- 概要：三角群の左上ブロックの 1 との差は小さい三角部分環に入る。
方針：恒等行列の制限と許される成分・係数イデアル条件を制限する。
規約：KST Claim 4.15。使われ方：小さい実三角群の値域条件。 -/
lemma triangularBlockGroup_dropLast_mem (n m : ℕ) (J : TwoSidedIdeal R)
    (g : triangularBlockGroup n (m + 1) J) :
    matrixDropLast (g.val : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) - 1 ∈
      blockPatternSubring (n + m) n J := by
  have he : matrixDropLast (g.val : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) - 1 =
      matrixDropLast ((g.val : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) - 1) := by
    rw [← matrixDropLast_one]
    rfl
  rw [he]
  constructor
  · intro i j hij
    exact g.property.1.1 i.castSucc j.castSucc (by simpa only [Fin.castSucc_lt_castSucc_iff, Fin.val_castSucc] using hij)
  · intro i j
    exact g.property.1.2 i.castSucc j.castSucc

/-- 概要：実三角群の左上ブロックは実単位。
方針：逆元の左上ブロックを逆に使い、最終行の恒等性で積を比較する。
規約：KST Claim 4.15。使われ方：小さい群への実射影。 -/
def triangularBlockGroupDropLastUnit (n m : ℕ) (J : TwoSidedIdeal R)
    (g : triangularBlockGroup n (m + 1) J) :
    (Matrix (Fin (n + m)) (Fin (n + m)) R)ˣ where
  val := matrixDropLast g.val.val
  inv := matrixDropLast (g⁻¹).val.val
  val_inv := by
    rw [← matrixDropLast_mul _ _ (triangularBlockGroup_lastRow n m J (g⁻¹))]
    have he := congrArg (fun u : (Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R)ˣ ↦ u.val)
      (mul_inv_cancel g.val)
    change matrixDropLast (g.val.val * (g.val⁻¹).val) = 1
    simp only [Units.val_mul, Units.val_one] at he
    rw [he, matrixDropLast_one]
  inv_val := by
    rw [← matrixDropLast_mul _ _ (triangularBlockGroup_lastRow n m J g)]
    have he := congrArg (fun u : (Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R)ˣ ↦ u.val)
      (inv_mul_cancel g.val)
    change matrixDropLast ((g.val⁻¹).val * g.val.val) = 1
    simp only [Units.val_mul, Units.val_one] at he
    rw [he, matrixDropLast_one]

/-- 概要：最後の補助座標を落とす実三角群準同型。
方針：左上ブロックの実単位と、元・逆の係数所属を束ねる。
規約：KST Claim 4.15。使われ方：実半直積比較の基底成分。 -/
def triangularBlockGroupDropLast (n m : ℕ) (J : TwoSidedIdeal R) :
    triangularBlockGroup n (m + 1) J →* triangularBlockGroup n m J where
  toFun g := ⟨triangularBlockGroupDropLastUnit n m J g,
    triangularBlockGroup_dropLast_mem n m J g,
    triangularBlockGroup_dropLast_mem n m J (g⁻¹)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact matrixDropLast_one
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact matrixDropLast_mul g.val.val h.val.val (triangularBlockGroup_lastRow n m J h)

end SerrePositivity.KST.ProExcision
