module

public import SerrePositivity.KST.DerivedGeometry.EmbeddedChainWindowSequence

/-!
概要：完全な小さい窓の列を自然数添字の鎖複体へ組み立てる。
方針：初期右項と順次の左項を項とし、選んだ先行微分で結ぶ。
規約：初項以外での完全性と全項の埋め込みを実際に証明する。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の非輪状部分複体の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G)
  {A : ChainComplex C ℕ} {Q : C} (W : EmbeddedChainWindow A Q 0)
  (hA : ∀ n : ℕ, A.ExactAt (n + 1))

/--
概要：小さい窓の列の各鎖次数の対象。
方針：零次数には初期右項、正次数には各窓の左項を置く。
規約：自然数添字。
使われ方：Stacks 19.12.2、TT §3 の上に有界な部分複体。
-/
def smallExactChainTerm : ℕ → C
  | 0 => W.right
  | n + 1 => (embeddedChainWindowSequence G hG W hA n).left

/--
概要：小さい窓の列の隣接微分。
方針：各窓の具体的な微分を用いる。
規約：次の窓の右項は前の左項と同一。
使われ方：Stacks 19.12.2、TT §3 の鎖複体の組み立て。
-/
def smallExactChainDifferential : ∀ n : ℕ,
    smallExactChainTerm G hG W hA (n + 1) ⟶ smallExactChainTerm G hG W hA n
  | 0 => W.d
  | n + 1 => (embeddedChainWindowSequence G hG W hA (n + 1)).d

/--
概要：小さい窓の列が与える自然数添字の鎖複体。
方針：各窓で証明された微分の合成零を使う。
規約：最上位の零次数の完全性は初期微分の全射性から別に得る。
使われ方：Stacks 19.12.2、TT §3 の小さい非輪状部分複体。
-/
def smallExactChainTail : ChainComplex C ℕ :=
  ChainComplex.of (smallExactChainTerm G hG W hA) (smallExactChainDifferential G hG W hA)
    (by
      intro n
      cases n with
      | zero => exact W.extend_zero G hG (hA 0)
      | succ n =>
        exact (embeddedChainWindowSequence G hG W hA (n + 1)).extend_zero G hG (hA (n + 1)))

/--
概要：組み立てた鎖複体の隣接微分は選んだ窓の微分に一致する。
方針：ChainComplex.of の隣接微分公式を使う。
規約：全自然数次数。
使われ方：Stacks 19.12.2、TT §3 の窓ごとの完全性との照合。
-/
lemma smallExactChainTail_d (n : ℕ) :
    (smallExactChainTail G hG W hA).d (n + 1) n =
      smallExactChainDifferential G hG W hA n :=
  ChainComplex.of_d _ _ _

end SerrePositivity.KST.DerivedGeometry
