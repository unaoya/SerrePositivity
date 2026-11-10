module
public import SerrePositivity.KST.ProExcision.Lemma416Data
public import SerrePositivity.KST.ProExcision.ConstructionA5

/-!
# Lemma 4.16 の非同変な実帰納ホモトピー

概要：実ブロック群、μ 版 A.5、A.6 の共役比較を使い、右乗法を m 次で定数と比較する。
方針：帰納仮定を C(P) 内に保ち、C(Q) の0次入力と組み合わせ、augmentation 補正を相殺する。
規約：KST Lemma 4.16 の非可換再記述。外部行列作用の同変性は別工程で接続する。
使われ方：同変な帰納ホモトピーの下層。非同変版だけで Lemma 4.16 完了としない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {R : Type u} [Ring R]

/-- 概要：m 次ホモトピーの区間射を保ったまま両端の等式で移す。
方針：実区間射をそのまま使い、成分の端点等式だけを連結する。
規約：KST A.3・4.16、等式輸送を端点の証明欄に留める。
使われ方：A.5・A.6 の実群準同型の端点の同定。 -/
def LinearizedMHomotopy.congr {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    {f g f' g' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D} {m : ℕ}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) (hf : f = f') (hg : g = g') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f' g' m where
  h := H.h
  h₀ n hn := (H.h₀ n hn).trans (congrArg (fun t ↦ t.app (op ⦋n⦌)) hf)
  h₁ n hn := (H.h₁ n hn).trans (congrArg (fun t ↦ t.app (op ⦋n⦌)) hg)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (congr)

/-- 概要：Lemma 4.16 の非同変な実帰納段階。
方針：因子内の m 次入力と Q の0次入力へ μ 版 A.5 を適用し、A.6 と連結して相殺する。
規約：非被約 C(H)、A.5 の右辺の augmentation 補正、非可換な実群。
使われ方：全 m の実帰納ホモトピー。外部行列作用の同変性を含めない。 -/
def lemma416HomotopyStep (n m : ℕ) (J : TwoSidedIdeal R) (a : J)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (lastRightColumnHom n m J (a : R)))
      (groupLinearizedMap (1 : Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 1) J)) m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (lastRightColumnHom n (m + 1) J (a : R)))
      (groupLinearizedMap (1 : Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 2) J)) (m + 1) := by
  let d := lemma416GroupData n m J (a : R)
  let hA := constructionA5 d m 0 h (groupZeroMHomotopy (MonoidHom.id (Multiplicative (Fin n → J))))
  have hend : groupLinearizedMap d.left + groupLinearizedMap d.right - groupLinearizedMap 1 =
      groupLinearizedMap (auxiliaryBlockColumnHom n m J) +
        groupLinearizedMap (lastRightColumnHom n (m + 1) J (a : R)) - groupLinearizedMap 1 := by
    dsimp only [d]
    rw [lemma416GroupData_left, lemma416GroupData_right]
    abel
  let hA' := hA.congr rfl hend
  let hC := groupConjugationMHomotopy (auxiliaryBlockColumnHom n m J) (auxiliaryBlockUnit n m J a) (m + 1)
  have hprod : groupLinearizedMap ((inverseConjugation (auxiliaryBlockUnit n m J a)).comp
      (auxiliaryBlockColumnHom n m J)) = groupLinearizedMap d.product :=
    congrArg groupLinearizedMap (lemma416GroupData_product n m J a).symm
  exact ((hC.congr rfl hprod).trans hA').cancel_augmentation

/-- 概要：右乗法の列は実三角ブロック群内で m 次ホモロジー定数となる非同変比較を持つ。
方針：零次を唯一の頂点の比較で開始し、実 μ と共役による帰納段階を繰り返す。
規約：KST Lemma 4.16 の非可換版の非同変部分。外部作用・関手性は別の性質。
使われ方：行列同変性を付けて A.4 と Proposition 4.14 へ渡す前の実ホモトピー。 -/
def lemma416Homotopy (n : ℕ) (J : TwoSidedIdeal R) (a : J) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (lastRightColumnHom n m J (a : R)))
      (groupLinearizedMap (1 : Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 1) J)) m :=
  Nat.rec (groupZeroMHomotopy (lastRightColumnHom n 0 J (a : R)))
    (fun m h ↦ lemma416HomotopyStep n m J a h) m

end SerrePositivity.KST.ProExcision
