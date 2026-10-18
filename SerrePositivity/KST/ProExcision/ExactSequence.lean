module

public import SerrePositivity.KST.ProExcision.FiveLemma

@[expose] public section

/-!
# レベル長完全列を塔へ持ち上げる

概要：自然なレベル完全列の族を次数別の加群の塔へ組み立てる。
方針：レベルごとの完全性と遷移の自然性をそのまま保持する。
規約：fiber 長完全列自体は K-L9 の入力であり、ここで存在を仮定せずに作らない。
使われ方：正本 §2.6 L1、KST Lemma 4.6 の長完全列の比較。
-/

universe u w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory

variable (R : Type u) [Ring R] (I : Type w) (next : I → I)

/-- 概要：遷移と両立するレベル完全列の族。
方針：対象、微分、遷移、完全性を数学的データとして保持する。
規約：next は長完全列の次の項を指定し、次数の符号規約を固定しない。
使われ方：K-L9 の fiber 長完全列から L1 を構成する入力。 -/
structure LevelwiseExactSequence where
  obj : ℕ → I → ModuleCat.{u} R
  d : ∀ n i, obj n i ⟶ obj n (next i)
  transition : ∀ {m n : ℕ}, n ≤ m → ∀ i, obj m i ⟶ obj n i
  transition_self : ∀ n i, transition (le_refl n) i = 𝟙 (obj n i)
  transition_comp : ∀ {k m n} (hm : m ≤ k) (hn : n ≤ m) i,
    transition hm i ≫ transition hn i = transition (hn.trans hm) i
  naturality : ∀ {m n} (h : n ≤ m) i,
    transition h i ≫ d n i = d m i ≫ transition h (next i)
  exact : ∀ n i, Function.Exact (d n i).hom (d n (next i)).hom

/-- 概要：塔の圏でのレベル完全列。
方針：各項を塔、微分をレベル射とする。
規約：完全性は各レベルでの完全性を意味する。
使われ方：L1 の出力と L2 の五項部分の抽出。 -/
structure ExactTowerSequence where
  obj : I → Tower (ModuleCat.{u} R)
  d : ∀ i, LevelHom (obj i) (obj (next i))
  exact : ∀ n i, Function.Exact ((d i).app n).hom ((d (next i)).app n).hom

variable {R I next}

/-- 概要：自然なレベル完全列を塔の完全列に組み立てる。
方針：遷移の律と微分の自然性をそのまま塔に移す。
規約：レベル長完全列の存在を結論に隠さず、具体的な族を入力とする。
使われ方：正本 §2.6 L1、K-L9 からの長完全列の受け入れ。 -/
def LevelwiseExactSequence.toTower (S : LevelwiseExactSequence R I next) :
    ExactTowerSequence R I next where
  obj i := {
    obj n := S.obj n i
    transition h := S.transition h i
    transition_self n := S.transition_self n i
    transition_comp hm hn := S.transition_comp hm hn i }
  d i := { app n := S.d n i, naturality h := S.naturality h i }
  exact n i := S.exact n i

/-- 概要：長完全列から連続する五項を抽出する。
方針：next を四回反復する。規約：端点に追加の完全性は要求しない。
使われ方：KST §4 の fiber 長完全列に対する pro 五項補題。 -/
def ExactTowerSequence.fiveTerm (S : ExactTowerSequence R I next) (i : I) :
    FiveTerm R where
  A := S.obj i
  B := S.obj (next i)
  C := S.obj (next (next i))
  D := S.obj (next (next (next i)))
  E := S.obj (next (next (next (next i))))
  ab := S.d i
  bc := S.d (next i)
  cd := S.d (next (next i))
  de := S.d (next (next (next i)))
  exactB n := S.exact n i
  exactC n := S.exact n (next i)
  exactD n := S.exact n (next (next i))

end SerrePositivity.KST.ProExcision
