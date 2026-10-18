module
public import SerrePositivity.KST.ProExcision.ActionRestriction

/-!
# Lemma 4.16 から相対半直積ホモロジーの零化

概要：群状モノイドの行列表示に沿って作用を制限し、右乗法の相対ホモロジー写像を零化する。
方針：実同変 m 次ホモトピーを A.4 の証明済み定理に渡す。
規約：KST Claim 4.15・Proposition 4.14 の前段。H_* の自然な複体模型だけを K-L2 の明示的界面として借りる。
使われ方：ĜL の作用による相対零化を安定化する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 概要：行列表示に沿って制限した右乗法は実同変 m 次で定数比較を持つ。
方針：構成済みの全行列同変比較を作用の制限へ移す。
規約：KST Lemma 4.16、G の行列表示のみを入力する。
使われ方：群状 ĜL の相対零化への入力。 -/
def lemma416_restrict (I : SimplicialIdealData.{u}) (a : I.ideal (op ⦋0⦌)) (n m : ℕ)
    {G : SimplicialObject MonCat.{u}} (ρ : G ⟶ I.matrixMonoid n) :
    HomologicallyMConstant ((I.rightColumnActionHom a n m).restrict ρ) m :=
  (lemma416 I a n m).restrict ρ

/-- 概要：群状モノイドの行列表示の下で右乗法の相対半直積ホモロジー写像は次数 ≤m で零。
方針：実同変比較を Lemma A.4 に適用する。
規約：KST Claim 4.15・Proposition 4.14 の非可換再記述の前段。
H_* の関手と自然な複体模型は所有レーンの入力であり、相対零化は仮定しない。
使われ方：実ブロック群から安定一般線形モノイドへの射を後合成して Claim 4.15 を得る。 -/
theorem lemma416_relative_zero (I : SimplicialIdealData.{u}) (a : I.ideal (op ⦋0⦌)) (n m : ℕ)
    {G : SimplicialObject MonCat.{u}} (ρ : G ⟶ I.matrixMonoid n) (hG : SimplicialMonoid.IsGrouplike G)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) (hi : i ≤ m) :
    relativeBarMap F ((I.rightColumnActionHom a n m).restrict ρ) = 0 :=
  lemmaA4 F hF M hG _ (lemma416_restrict I a n m ρ) hi

end SerrePositivity.KST.ProExcision
