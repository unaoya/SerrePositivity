module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGLGrouplike

/-!
# 非単位環の ĜL 作用に対する Lemma 4.16 の相対零化

概要：一般の非単位単体環の実 ĜL 作用について低次の相対写像を零化する。
方針：ĜL の行列表示と証明済みの群状性を Lemma A.4 へ渡す。
規約：KST Claim 4.15 の三角ブロック模型への因子化。H_* の模型のみ K-L2 から借りる。
使われ方：安定化の前に必要な相対零化の実入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：非単位環の実 ĜL 作用に対する右乗法の低次相対写像は零。
方針：単位化の実模型・行列表現・群状性を既証明の相対零化へ適用する。
規約：KST Lemma 4.16・Claim 4.15。群状性や零化を仮定せず、H_* 模型のみ明示する。
使われ方：三角群の半直積からの実比較射を後合成する。 -/
theorem nonUnitalLemma416_relative_zero (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n m : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) (hi : i ≤ m) :
    relativeBarMap F
      ((I.standardIdeal.rightColumnActionHom (I.standardElement a) n m).restrict
        (I.hatGLRepresentation n)) = 0 :=
  lemma416_relative_zero I.standardIdeal (I.standardElement a) n m
    (I.hatGLRepresentation n) (I.hatGL_isGrouplike n) F hF M hi

end SerrePositivity.KST.ProExcision
