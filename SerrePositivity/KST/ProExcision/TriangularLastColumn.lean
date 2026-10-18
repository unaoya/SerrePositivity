module
public import SerrePositivity.KST.ProExcision.TriangularDropLast

/-!
# 三角ブロック群の最終列の係数と積

概要：最終列を係数イデアル内の列として取り出し、半直積の積の法則を証明する。
方針：非対角成分は 1 との差に等しく、最終行は恒等行であることを使う。
規約：KST Claim 4.15 の実半直積への分解、非可換係数を許す。
使われ方：三角群から列群を含む半直積への実比較。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R]

/-- 概要：三角群の最終列の前半は係数イデアルに入る。
方針：最終対角成分より前の成分では恒等行列が零である。
規約：KST Claim 4.15。使われ方：列をイデアルの元として取り出す。 -/
lemma triangularBlockGroup_lastColumn_mem (n m : ℕ) (J : TwoSidedIdeal R)
    (g : triangularBlockGroup n (m + 1) J) (i : Fin (n + m)) :
    matrixLastColumn g.val.val i ∈ J := by
  have h := g.property.1.2 i.castSucc (Fin.last (n + m))
  simpa [matrixLastColumn, Matrix.sub_apply, Matrix.one_apply, Fin.castSucc_ne_last] using h

/-- 概要：実三角群の最終列をイデアル内の列として取る。
方針：各成分の所属証明を付ける。
規約：KST Claim 4.15。使われ方：半直積のファイバー成分。 -/
def triangularBlockGroupLastColumn (n m : ℕ) (J : TwoSidedIdeal R)
    (g : triangularBlockGroup n (m + 1) J) : Fin (n + m) → J :=
  fun i ↦ ⟨matrixLastColumn g.val.val i, triangularBlockGroup_lastColumn_mem n m J g i⟩

/-- 概要：三角群の単位元の最終列は零。
方針：恒等行列の非対角成分を計算する。
規約：KST Claim 4.15。使われ方：半直積の単位保存。 -/
lemma triangularBlockGroupLastColumn_one (n m : ℕ) (J : TwoSidedIdeal R) :
    triangularBlockGroupLastColumn n m J 1 = 0 := by
  funext i
  apply Subtype.ext
  exact congrFun matrixLastColumn_one i

/-- 概要：三角群の積の最終列は左上ブロックの行列作用による半直積の法則に従う。
方針：実行列の最終列の積の公式をイデアル内の各成分へ戻す。
規約：KST Claim 4.15、積の順は v+M v′。
使われ方：三角群の実半直積分解の乗法保存。 -/
lemma triangularBlockGroupLastColumn_mul (n m : ℕ) (J : TwoSidedIdeal R)
    (g h : triangularBlockGroup n (m + 1) J) :
    triangularBlockGroupLastColumn n m J (g * h) =
      triangularBlockGroupLastColumn n m J g +
        (idealMatrixAction (n + m) J
          (triangularBlockGroupDropLast n m J g).val.val
          (Multiplicative.ofAdd (triangularBlockGroupLastColumn n m J h))).toAdd := by
  funext i
  apply Subtype.ext
  have hdiag : h.val.val (Fin.last (n + m)) (Fin.last (n + m)) = 1 := by
    simpa using triangularBlockGroup_lastRow n m J h (Fin.last (n + m))
  have he := congrFun (matrixLastColumn_mul g.val.val h.val.val hdiag) i
  exact he

end SerrePositivity.KST.ProExcision
