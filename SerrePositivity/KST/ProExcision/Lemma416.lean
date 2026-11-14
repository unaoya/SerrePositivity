module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.SimplicialMatrixActions
public import SerrePositivity.KST.ProExcision.Lemma416Equivariance
public import SerrePositivity.KST.ProExcision.LemmaA4

/-!
# 非可換な単体的イデアル上の Lemma 4.16

概要：右乗法の実射は、全行列作用に同変な実 m 次ホモトピーによって自明射と比較できる。
方針：実ブロック群内の関手的・同変な離散環上の帰納構成を対角 bar へ移す。
規約：KST Lemma 4.16 の非可換再記述。非被約 C(H)、A.5 の augmentation 補正を保つ。
使われ方：Lemma A.4 の実入力として相対ホモロジーを零化する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単体環上の実帰納ホモトピーは単体的全行列作用に同変。
方針：係数次数 k の離散環上の同変性を、同じ nerve 次数 k で評価する。
規約：KST Lemma 4.16、非可換な係数と非可逆な全行列。
使われ方：HomologicallyMConstant の実同変条件。 -/
lemma simplicialLemma416Homotopy_equivariant (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) (n m : ℕ) :
    LinearizedCylinderEquivariant (barSetAction (I.columnMatrixAction n))
      (barSetAction (I.triangularMatrixAction n (m + 1))) (simplicialLemma416Homotopy I a n m).h := by
  intro k M
  exact lemma416Homotopy_equivariant n (I.ideal k) (I.vertexElement a k) m k M

/-- 概要：非可換な単体的イデアル上の右乗法の列は homologically m-constant。
方針：構成した対角 C(H) の実 m 次ホモトピーと全行列同変性を束ねる。
規約：KST Lemma 4.16 の非可換再記述、φ(v)=va。中心性・単射性はこの補題には不要。
使われ方：Lemma A.4 により相対半直積ホモロジーの零化を得る。 -/
def lemma416 (I : SimplicialIdealData.{u}) (a : I.ideal (op ⦋0⦌)) (n m : ℕ) :
    HomologicallyMConstant (I.rightColumnActionHom a n m) m where
  homotopy := simplicialLemma416Homotopy I a n m
  equivariant := simplicialLemma416Homotopy_equivariant I a n m

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 4.16" (partial := component) "仮定：単体イデアルまたは非単位的単体環の行列・列作用（原典と一致）。結論：同変な m 次までの定値ホモトピーを行列模型で与える。原典の一般線形群の係数つき鎖への全比較を含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.lemma416
