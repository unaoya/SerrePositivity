module
public import SerrePositivity.KST.ProExcision.ActionNerveCoordinates

/-!
# 作用圏の始点と射影の語による座標

概要：作用圏の射列を、始点と作用モノイドへの射影の射列で記述する。
方針：隣接ラベルの全単射と Segal 座標の全単射を組み合わせる。
規約：KST Lemma A.4 の線形化された係数 bar の準備。
使われ方：任意の線形係数の写像を、G の語を固定して bar へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G X : Type u} [Monoid G] [MulAction G X]

/-- 概要：作用圏の射列の始点と作用モノイドへの射影。
方針：対象0と射影関手との合成を取る。
規約：KST Lemma A.4。使われ方：線形係数の bar の語の固定。 -/
def actionNerveWordCoordinates {n : ℕ} (p : (nerve (ActionObject G X)) _⦋n⦌) :
    X × (nerve (SingleObj G)) _⦋n⦌ := ((p.obj 0).val, p ⋙ actionCategoryProjection)

/-- 概要：始点と射影の語の座標は単射。
方針：隣接ラベルの座標の単射性へ帰着する。
規約：KST Lemma A.4。使われ方：bar の単体の自然性の証明。 -/
lemma actionNerveWordCoordinates_injective (n : ℕ) :
    Function.Injective (actionNerveWordCoordinates (G := G) (X := X) (n := n)) := by
  intro p q h
  apply actionNerveCoordinates_injective n
  apply Prod.ext
  · have h₀ : (p.obj 0).val = (q.obj 0).val := congrArg Prod.fst h
    exact h₀
  · exact congrArg (monoidWordLabels (MonCat.of G)) (congrArg Prod.snd h)

/-- 概要：作用圏の単体と始点×射影の語の全単射。
方針：隣接ラベルの座標の全単射を経由する。
規約：KST Lemma A.4。使われ方：語を固定した係数の基底の包含。 -/
def actionNerveWordEquiv (n : ℕ) : (nerve (ActionObject G X)) _⦋n⦌ ≃
    X × (nerve (SingleObj G)) _⦋n⦌ :=
  Equiv.ofBijective actionNerveWordCoordinates
    ⟨actionNerveWordCoordinates_injective n, by
      rintro ⟨x, w⟩
      let p := (actionNerveEquiv (G := G) (X := X) n).symm
        (x, monoidWordLabels (MonCat.of G) w)
      have hp := (actionNerveEquiv (G := G) (X := X) n).apply_symm_apply
        (x, monoidWordLabels (MonCat.of G) w)
      have h₀ : (p.obj 0).val = x := congrArg Prod.fst hp
      refine ⟨p, Prod.ext h₀ ?_⟩
      exact (monoidWordEquiv (MonCat.of G) n).injective (congrArg Prod.snd hp)⟩

/-- 概要：語を固定した作用圏の基底単体。
方針：始点と語の座標の逆写像。
規約：KST Lemma A.4。使われ方：線形係数を bar の単体へ送る。 -/
abbrev actionNerveWordSection {n : ℕ} (x : X) (w : (nerve (SingleObj G)) _⦋n⦌) :=
  (actionNerveWordEquiv (G := G) (X := X) n).symm (x, w)

/-- 概要：語を固定した単体の始点は指定された元。
方針：全単射の右逆の第一成分を取る。
規約：KST Lemma A.4。使われ方：係数の射の両端条件。 -/
@[simp] lemma actionNerveWordSection_source {n : ℕ}
    (x : X) (w : (nerve (SingleObj G)) _⦋n⦌) :
    ((actionNerveWordSection x w).obj 0).val = x :=
  congrArg Prod.fst ((actionNerveWordEquiv n).apply_symm_apply (x, w))

/-- 概要：語を固定した単体の射影は指定された語。
方針：全単射の右逆の第二成分を取る。
規約：KST Lemma A.4。使われ方：単体射に沿う語の移送の検証。 -/
@[simp] lemma actionNerveWordSection_projection {n : ℕ}
    (x : X) (w : (nerve (SingleObj G)) _⦋n⦌) :
    actionNerveWordSection x w ⋙ actionCategoryProjection = w :=
  congrArg Prod.snd ((actionNerveWordEquiv n).apply_symm_apply (x, w))

end SerrePositivity.KST.ProExcision
