module
public import SerrePositivity.KST.ProExcision.IdealColumnBlockInclusion

/-!
# 右乗法の実最終列の二成分

概要：右乗法を三角群の最終列へ入れた射の左上ブロックと列成分を同定する。
方針：実列の成分計算と、零埋め列のイデアルからの忘却を使う。
規約：KST Claim 4.15・Lemma 4.16、右乗法の順を保つ。
使われ方：因子化した射が通常の有限 rank の写像であることを示す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：右乗法の最終列の左上ブロックは恒等行列。
方針：実射の値を 1 と最終列の和に展開する。
規約：KST Claim 4.15。使われ方：基底の写像の同定。 -/
lemma lastRightColumn_dropLast (n m : ℕ) (J : TwoSidedIdeal R) (a : R)
    (v : Multiplicative (Fin n → J)) :
    matrixDropLast (lastRightColumnHom n m J a v).val.val =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) := by
  change matrixDropLast (1 + blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m))
    (fun i ↦ ((idealVectorRightHom J (Fin n) a v).toAdd i : R))) = _
  exact matrixDropLast_one_add_lastColumn n m _

/-- 概要：右乗法の最終列は v↦va の後の零埋め列に等しい。
方針：周囲環の各成分で実最終列の式とイデアルの零埋めの式を比較する。
規約：KST Claim 4.15、a の中心性や単射性はこの比較に不要。
使われ方：相対零化した実合成の通常の列写像との同定。 -/
lemma lastRightColumn_lastColumn (n m : ℕ) (J : TwoSidedIdeal R) (a : R)
    (v : Multiplicative (Fin n → J)) :
    triangularBlockGroupLastColumn n m J (lastRightColumnHom n m J a v) =
      columnBlockInclusion J n m (idealVectorRightHom J (Fin n) a v).toAdd := by
  funext i
  apply Subtype.ext
  have h := congrFun (matrixLastColumn_one_add_lastColumn n m
    (fun i ↦ ((idealVectorRightHom J (Fin n) a v).toAdd i : R))) i
  have hc := congrFun (columnBlockInclusion_coe J n m (idealVectorRightHom J (Fin n) a v).toAdd) i
  exact h.trans hc.symm

end SerrePositivity.KST.ProExcision
