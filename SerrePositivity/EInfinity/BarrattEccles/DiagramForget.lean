module

public import SerrePositivity.EInfinity.BarrattEccles.DiagramModel
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# 小さい E 代数図式の導来忘却

概要：BM 命題 4.1 の図式モデルから、同じ添字圏の複体図式の局所化へ忘却する。
方針：頂点ごとの擬同型を保存・反映し、通常の局所化の普遍性を使う。
規約：元の図式と射を保ち、図式の弱同値を反転する任意の局所化を許す。
使われ方：E2a-4 の一般図式の極限比較と E2b の導来忘却の界面。
-/

@[expose] public section

noncomputable section

universe u v w v' w'

namespace SerrePositivity.EInfinity.BarrattEccles.Diagram

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：小さい E 代数図式を同じ添字の複体図式へ忘却する（BM §1）。
方針：代数の忘却関手を後合成する。
規約：添字の対象と射を変更しない。
使われ方：一般図式の底の比較。 -/
def forget : (K ⥤ (operad A).Algebra) ⥤ (K ⥤ Complex A) :=
  (Functor.whiskeringRight K _ _).obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))

/-- 概要：複体図式の頂点ごとの擬同型のクラス（Hovey §2.3）。
方針：すべての評価で擬同型を要求する。
規約：この定義に複体図式のモデル構造は不要。
使われ方：導来忘却の値の局所化で反転する射。 -/
def objectwiseQuasiIsos : MorphismProperty (K ⥤ Complex A) :=
  fun _ _ f => ∀ k, QuasiIso (f.app k)

/-- 概要：E 代数図式の弱同値は図式忘却で作られる（BM 命題 4.1）。
方針：評価族の転送モデル構造の右類を展開する。
規約：具体的なモデル構造のフィールドを指定する。
使われ方：モデル圏の局所化と頂点ごとの擬同型の局所化を接続する。 -/
lemma projectiveModelCategory_weakEquivalences :
    @HomotopicalAlgebra.weakEquivalences (K ⥤ (operad A).Algebra) _
      (projectiveModelCategory A K).categoryWithWeakEquivalences =
        (objectwiseQuasiIsos A K).inverseImage (forget A K) := rfl

variable {H : Type w} [Category.{v} H]
  (Q : (K ⥤ Complex A) ⥤ H) [Q.IsLocalization (objectwiseQuasiIsos A K)]

/-- 概要：底の局所化へ続く図式忘却はすべての図式弱同値を反転する（BM §1）。
方針：同じ頂点ごとの擬同型を値の局所化で反転する。
規約：弱同値の逆像そのものを使う。
使われ方：具体的な導来忘却を構成する普遍性の入力。 -/
lemma forget_inverts : ((objectwiseQuasiIsos A K).inverseImage (forget A K)).IsInvertedBy
    (forget A K ⋙ Q) := by
  intro F G f hf
  exact Localization.inverts Q (objectwiseQuasiIsos A K) ((forget A K).map f) hf

variable {D : Type w'} [Category.{v'} D]
  (L : (K ⥤ (operad A).Algebra) ⥤ D)
  [L.IsLocalization ((objectwiseQuasiIsos A K).inverseImage (forget A K))]

/-- 概要：図式忘却の実際の右導来関手（BM §1、Hovey §1.3）。
方針：元の忘却はすべての弱同値を保つので、そのまま局所化へ降ろす。
規約：代数図式と複体図式の局所化は任意のものを許す。
使われ方：一般図式の導来忘却を置換に依存せず指定する。 -/
def localizedForget : D ⥤ H :=
  Localization.lift (forget A K ⋙ Q) (forget_inverts A K Q) L

/-- 概要：導来図式忘却は元の図式忘却と自然同型で比較できる（Hovey §1.3）。
方針：局所化の普遍性の因子分解同型を使う。
規約：元の図式全体で比較し、fibrant 置換は追加しない。
使われ方：導来忘却の値と射の具体的な計算。 -/
def localizedForgetComparison : forget A K ⋙ Q ≅ L ⋙ localizedForget A K Q L :=
  (Localization.fac (forget A K ⋙ Q) (forget_inverts A K Q) L).symm

/-- 概要：構成した図式忘却は実際の右導来関手の普遍性を持つ（Hovey §1.3）。
方針：弱同値を反転する関手の局所化は点ごとの左 Kan 拡張になる。
規約：右導来性を入力仮定として要求しない。
使われ方：一般 homotopy 極限比較の導来関手側の根拠。 -/
lemma localizedForget_isRightDerivedFunctor :
    (localizedForget A K Q L).IsRightDerivedFunctor
      (localizedForgetComparison A K Q L).hom
      ((objectwiseQuasiIsos A K).inverseImage (forget A K)) := by
  exact inferInstanceAs ((Localization.lift (forget A K ⋙ Q)
    (forget_inverts A K Q) L).IsRightDerivedFunctor
      (Localization.fac (forget A K ⋙ Q) (forget_inverts A K Q) L).inv _)

/-- 概要：図式忘却の点ごとの右導来関手は存在する（Hovey §1.3）。
方針：すべての図式弱同値を反転する事実から構成する。
規約：E 代数のモデル構造や局所化の選択を追加の存在仮定にしない。
使われ方：任意の小図式上の右導来忘却を使う。 -/
lemma forget_hasPointwiseRightDerivedFunctor :
    (forget A K ⋙ Q).HasPointwiseRightDerivedFunctor
      ((objectwiseQuasiIsos A K).inverseImage (forget A K)) :=
  Functor.hasPointwiseRightDerivedFunctor_of_inverts _ (forget_inverts A K Q)

end SerrePositivity.EInfinity.BarrattEccles.Diagram
